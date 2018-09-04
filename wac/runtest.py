#!/usr/bin/env python

from __future__ import print_function
import os, sys, re
import argparse, time
import signal, atexit, tempfile, subprocess

from subprocess import Popen, STDOUT, PIPE
from select import select

# Pseudo-TTY and terminal manipulation
import pty, array, fcntl, termios

IS_PY_3 = sys.version_info[0] == 3

debug_file = None
log_file = None

def debug(data):
    if debug_file:
        debug_file.write(data)
        debug_file.flush()

def log(data, end='\n'):
    if log_file:
        log_file.write(data + end)
        log_file.flush()
    print(data, end=end)
    sys.stdout.flush()

# TODO: do we need to support '\n' too
import platform
if platform.system().find("CYGWIN_NT") >= 0:
    # TODO: this is weird, is this really right on Cygwin?
    sep = "\n\r\n"
else:
    sep = "\r\n"
rundir = None

class Runner():
    def __init__(self, args, no_pty=False):
        #print "args: %s" % repr(args)
        self.no_pty = no_pty

        # Cleanup child process on exit
        atexit.register(self.cleanup)

        self.p = None
        env = os.environ
        env['TERM'] = 'dumb'
        env['INPUTRC'] = '/dev/null'
        env['PERL_RL'] = 'false'
        if no_pty:
            self.p = Popen(args, bufsize=0,
                           stdin=PIPE, stdout=PIPE, stderr=STDOUT,
                           preexec_fn=os.setsid,
                           env=env)
            self.stdin = self.p.stdin
            self.stdout = self.p.stdout
        else:
            # provide tty to get 'interactive' readline to work
            master, slave = pty.openpty()

            # Set terminal size large so that readline will not send
            # ANSI/VT escape codes when the lines are long.
            buf = array.array('h', [100, 200, 0, 0])
            fcntl.ioctl(master, termios.TIOCSWINSZ, buf, True)

            self.p = Popen(args, bufsize=0,
                           stdin=slave, stdout=slave, stderr=STDOUT,
                           preexec_fn=os.setsid,
                           env=env)
            # Now close slave so that we will get an exception from
            # read when the child exits early
            # http://stackoverflow.com/questions/11165521
            os.close(slave)
            self.stdin = os.fdopen(master, 'r+b', 0)
            self.stdout = self.stdin

        #print "started"
        self.buf = ""
        self.last_prompt = ""

    def read_to_prompt(self, prompts, timeout):
        end_time = time.time() + timeout
        while time.time() < end_time:
            [outs,_,_] = select([self.stdout], [], [], 1)
            if self.stdout in outs:
                new_data = self.stdout.read(1)
                new_data = new_data.decode("utf-8") if IS_PY_3 else new_data
                #print("new_data: '%s'" % new_data)
                debug(new_data)
                if self.no_pty:
                    self.buf += new_data.replace("\n", "\r\n")
                else:
                    self.buf += new_data
                self.buf = self.buf.replace("\r\r", "\r")
                for prompt in prompts:
                    regexp = re.compile(prompt)
                    match = regexp.search(self.buf)
                    if match:
                        end = match.end()
                        buf = self.buf[0:end-len(prompt)]
                        self.buf = self.buf[end:]
                        self.last_prompt = prompt
                        return buf
        return None

    def writeline(self, str):
        def _to_bytes(s):
            return bytes(s, "utf-8") if IS_PY_3 else s

        self.stdin.write(_to_bytes(str + "\n"))

    def cleanup(self):
        #print "cleaning up"
        if self.p:
            try:
                os.killpg(self.p.pid, signal.SIGTERM)
            except OSError:
                pass
            self.p = None

def assert_prompt(runner, prompts, timeout):
    # Wait for the initial prompt
    header = runner.read_to_prompt(prompts, timeout=timeout)
    if not header == None:
        if header:
            log("Started with:\n%s" % header)
    else:
        log("Did not one of following prompt(s): %s" % repr(prompts))
        log("    Got      : %s" % repr(r.buf))
        sys.exit(1)


### WebAssembly specific

parser = argparse.ArgumentParser(
        description="Run a test file against a WebAssembly interpreter")
parser.add_argument('--wast2wasm', type=str,
        default=os.environ.get("WAST2WASM", "wast2wasm"),
        help="Path to wast2wasm program")
parser.add_argument('--interpreter', type=str,
        default=os.environ.get("WA_CMD", "./wac"),
        help="Path to WebAssembly interpreter")
parser.add_argument('--no-cleanup', action='store_true',
        help="Keep temporary *.wasm files")

parser.add_argument('--rundir',
        help="change to the directory before running tests")
parser.add_argument('--start-timeout', default=10, type=int,
        help="default timeout for initial prompt")
parser.add_argument('--test-timeout', default=20, type=int,
        help="default timeout for each individual test action")
parser.add_argument('--no-pty', action='store_true',
        help="Use direct pipes instead of pseudo-tty")
parser.add_argument('--log-file', type=str,
        help="Write messages to the named file in addition the screen")
parser.add_argument('--debug-file', type=str,
        help="Write all test interaction the named file")

parser.add_argument('test_file', type=argparse.FileType('r'),
        help="a WebAssembly *.wast test file")


# regex patterns of tests to skip
C_SKIP_TESTS = (
        # names.wast
        'invoke \"~!',
        # conversions.wast
        'reinterpret_f.*nan',
        # float_misc.wast
        'f64.add.*0x1.fffffffffffffp\+969',
        # float_exprs.wast
        'nonarithmetic_nan_bitpattern.*03210' )
PY_SKIP_TESTS = (
        # names.wast
        'invoke \"~!',
        # conversions.wast
        '18446742974197923840.0',
        '18446744073709549568.0',
        '9223372036854775808',
        'reinterpret_f.*nan',
        # endianness
        '.const 0x1.fff' )

def read_forms(string):
    forms = []
    form = ""
    depth = 0
    line = 0
    pos = 0
    while pos < len(string):
        # Keep track of line number
        if string[pos] == '\n': line += 1

        # Handle top-level elements
        if depth == 0:
            # Add top-level comments
            if string[pos:pos+2] == ";;":
                end = string.find("\n", pos)
                if end == -1: end == len(string)
                forms.append(string[pos:end])
                pos = end
                continue

            # TODO: handle nested multi-line comments
            if string[pos:pos+2] == "(;":
                # Skip multi-line comment
                end = string.find(";)", pos)
                if end == -1:
                    raise Exception("mismatch multiline comment on line %d: '%s'" % (
                        line, string[pos:pos+80]))
                pos = end+2
                continue

            # Ignore whitespace between top-level forms
            if string[pos] in (' ', '\n', '\t'):
                pos += 1
                continue

        # Read a top-level form
        if string[pos] == '(': depth += 1
        if string[pos] == ')': depth -= 1
        if depth == 0 and not form:
            raise Exception("garbage on line %d: '%s'" % (
                line, string[pos:pos+80]))
        form += string[pos]
        if depth == 0 and form:
            forms.append(form)
            form = ""
        pos += 1
    return forms

def parse_const(val):
    if   val == '':
        return (None, '')
    type = val[0:3]
    if type in ["i32", "i64"]:
        if val[10:12] == "0x":
            return (int(val[10:], 16),
                    "%s:%s" % (val[10:].lower(), type))
        else:
            return (int(val[10:]),
                    "%s:%s" % (hex(int(val[10:])), type))
    elif type in ["f32", "f64"]:
        if val.find("nan:") >= 0:
            # TODO: how to handle this correctly
            return (float.fromhex(val[10:].split(':')[1]),
                    "%s:%s" % (val[10:].split(':')[0], type))
        elif val[10:12] == "0x" or val[10:13] == "-0x":
            return (float.fromhex(val[10:]),
                    "%.7g:%s" % (float.fromhex(val[10:]), type))
        else:
            return (float(val[10:]),
                    "%.7g:%s" % (float(val[10:]), type))
    else:
        raise Exception("invalid value '%s'" % val)

def int2uint32(i):
    return i & 0xffffffff

def int2int32(i):
    val = i & 0xffffffff
    if val & 0x80000000:
        return val - 0x100000000
    else:
        return val

def int2uint64(i):
    return i & 0xffffffffffffffff

def int2int64(i):
    val = i & 0xffffffffffffffff
    if val & 0x8000000000000000:
        return val - 0x10000000000000000
    else:
        return val


def num_repr(i):
    if isinstance(i, int) or isinstance(i, long):
        return re.sub("L$", "", hex(i))
    else:
        return "%.16g" % i

def hexpad16(i):
    return "0x%04x" % i

def hexpad24(i):
    return "0x%06x" % i

def hexpad32(i):
    return "0x%08x" % i

def hexpad64(i):
    return "0x%016x" % i

def invoke(r, args, cmd):
    r.writeline(cmd)

    return r.read_to_prompt(['\r\nwebassembly> ', '\nwebassembly> '],
            timeout=args.test_timeout)

def test_assert(r, opts, mode, cmd, expected):
    log("Testing(%s) %s = %s" % (mode, cmd, expected))

    out = invoke(r, opts, cmd)
    outs = [''] + out.split('\n')[1:]
    out = outs[-1]

    if mode=='trap':
        o = re.sub('^Exception: ', '', out)
        e = re.sub('^Exception: ', '', expected)
        if o.find(e) >= 0 or e.find(o) >= 0:
            return True

    expects = set([expected])
    m0 = re.search("^(-?[0-9\.e-]+):f32$", expected)
    if m0:
        if m0.group(1) == "-0":
            expects.add("0:f32")
        expects.add('%f:f32' % float(m0.group(1)))
        expects.add('%f:f32' % round(float(m0.group(1)),5))
    if expected == "-nan:f32":
        expects.add("nan:f32")
    if expected == "nan:f32":
        expects.add("-nan:f32")
    if expected == "-nan:f64":
        expects.add("nan:f64")
    if expected == "nan:f64":
        expects.add("-nan:f64")

    # munge the output some
    out = re.sub("L:i32$", ':i32', out)
    out = re.sub("L:i64$", ':i64', out)
    results = set([out])
    # create alternate representations
    m1 = re.search("^(-?[0-9a-fx]+):i32$", out)
    m2 = re.search("^(-?[0-9a-fx]+):i64$", out)
    m3 = re.search("^(-?[0-9\.e-]+):f32$", out)
    m4 = re.search("^(-?0x[0-9a-fp+\.]+):f32$", out)
    m5 = re.search("^(-?[0-9\.e-]+):f64$", out)
    m6 = re.search("^(-?0x[0-9a-fp+\.]+):f64$", out)
    if m1:
        val = int(m1.group(1), 16)
        results.add(num_repr(int2int32(val))+":i32")
        results.add(num_repr(int2uint32(val))+":i32")
        results.add(hexpad16(int2uint32(val))+":i32")
        results.add(hexpad24(int2uint32(val))+":i32")
        results.add(hexpad32(int2uint32(val))+":i32")
    elif m2:
        val = int(m2.group(1), 16)
        results.add(num_repr(int2int64(val))+":i64")
        results.add(num_repr(int2uint64(val))+":i64")
        results.add(hexpad32(int2uint64(val))+":i64")
        results.add(hexpad64(int2uint64(val))+":i64")
    elif m3:
        val = float(m3.group(1))
        if re.search("^.*\.0+$", m3.group(1)):
            # Zero
            results.add('%d:f32' % int(val))
            results.add('%.7g:f32' % val)
        else:
            results.add('%.7g:f32' % val)
    elif m4:
        val = float.fromhex(m4.group(1))
        results.add("%f:f32" % val)
        results.add("%.7g:f32" % val)
    elif m5:
        val = float(m5.group(1))
        if re.search("^.*\.0+$", m5.group(1)):
            # Zero
            results.add('%d:f64' % int(val))
            results.add('%.7g:f64' % val)
        else:
            results.add('%.7g:f64' % val)
    elif m6:
        val = float.fromhex(m6.group(1))
        results.add("%f:f64" % val)
        results.add("%.7g:f64" % val)

    if not expects.intersection(results):
        raise Exception("Failed:\n  expected: '%s' %s\n  got: '%s' %s" % (
            expected, expects, out, results))

    return True

def test_assert_return(r, opts, form):
    # params, return
    m = re.search('^\(assert_return\s+\(invoke\s+"((?:[^"]|\\\")*)"\s+(\(.*\))\s*\)\s*(\([^)]+\))\s*\)\s*$', form, re.S)
    if not m:
        # no params, return
        m = re.search('^\(assert_return\s+\(invoke\s+"((?:[^"]|\\\")*)"\s*\)\s+()(\([^)]+\))\s*\)\s*$', form, re.S)
    if not m:
        # params, no return
        m = re.search('^\(assert_return\s+\(invoke\s+"([^"]*)"\s+(\(.*\))()\s*\)\s*\)\s*$', form, re.S)
    if not m:
        # no params, no return
        m = re.search('^\(assert_return\s+\(invoke\s+"([^"]*)"\s*()()\)\s*\)\s*$', form, re.S)
    if not m:
        raise Exception("unparsed assert_return: '%s'" % form)
    func = m.group(1)
    if m.group(2) == '':
        args = []
    else:
        args = [re.split(' +', v)[1] for v in re.split("\)\s*\(", m.group(2)[1:-1])]
    result, expected = parse_const(m.group(3)[1:-1])

    test_assert(r, opts, "return", "%s %s" % (func, " ".join(args)), expected)

def test_assert_trap(r, opts, form):
    # params
    m = re.search('^\(assert_trap\s+\(invoke\s+"([^"]*)"\s+(\(.*\))\s*\)\s*"([^"]+)"\s*\)\s*$', form)
    if not m:
        # no params
        m = re.search('^\(assert_trap\s+\(invoke\s+"([^"]*)"\s*()\)\s*"([^"]+)"\s*\)\s*$', form)
    if not m:
        raise Exception("unparsed assert_trap: '%s'" % form)
    func = m.group(1)
    if m.group(2) == '':
        args = []
    else:
        args = [re.split(' +', v)[1] for v in re.split("\)\s*\(", m.group(2)[1:-1])]
    expected = "Exception: %s" % m.group(3)

    test_assert(r, opts, "trap", "%s %s" % (func, " ".join(args)), expected)

def do_invoke(r, opts, form):
    # params
    m = re.search('^\(invoke\s+"([^"]+)"\s+(\(.*\))\s*\)\s*$', form)
    if not m:
        # no params
        m = re.search('^\(invoke\s+"([^"]+)"\s*()\)\s*$', form)
    if not m:
        raise Exception("unparsed invoke: '%s'" % form)
    func = m.group(1)
    if m.group(2) == '':
        args = []
    else:
        args = [re.split(' +', v)[1] for v in re.split("\)\s*\(", m.group(2)[1:-1])]

    log("Invoking %s(%s)" % (
        func, ", ".join([str(a) for a in args])))

    invoke(r, opts, "%s %s" % (func, " ".join(args)))

def skip_test(form, skip_list):
    for s in skip_list:
        if re.search(s, form):
            return True
    return False


if __name__ == "__main__":
    opts = parser.parse_args(sys.argv[1:])

    if opts.rundir: os.chdir(opts.rundir)

    if opts.log_file:   log_file   = open(opts.log_file, "a")
    if opts.debug_file: debug_file = open(opts.debug_file, "a")

    if opts.interpreter.endswith(".py"):
        SKIP_TESTS = PY_SKIP_TESTS
    else:
        SKIP_TESTS = C_SKIP_TESTS

    (t1fd, wast_tempfile) = tempfile.mkstemp(suffix=".wast")
    (t2fd, wasm_tempfile) = tempfile.mkstemp(suffix=".wasm")

    try:
        forms = read_forms(opts.test_file.read())
        r = None

        for form in forms:
            if  ";;" == form[0:2]:
                log(form)
            elif skip_test(form, SKIP_TESTS):
                log("Skipping test: %s" % form[0:60])
            elif re.match("^\(assert_trap\s+\(module", form):
                log("ignoring assert_trap around module")
                pass
            elif re.match("^\(assert_exhaustion\\b.*", form):
                log("ignoring assert_exhaustion")
                pass
            elif re.match("^\(assert_unlinkable\\b.*", form):
                log("ignoring assert_unlinkable")
                pass
            elif re.match("^\(assert_malformed\\b.*", form):
                log("ignoring assert_malformed")
                pass
            elif re.match("^\(assert_return[_a-z]*_nan\\b.*", form):
                log("ignoring assert_return_.*_nan")
                pass
            elif re.match(".*\(invoke\s+\$\\b.*", form):
                log("ignoring invoke $FOO")
                pass

            elif re.match("^\(module\\b.*", form):
                log("Writing WAST module to '%s'" % wast_tempfile)
                file(wast_tempfile, 'w').write(form)
                log("Compiling WASM to '%s'" % wasm_tempfile)
                cmd = [ opts.wast2wasm,
                        "--no-check",
                        wast_tempfile,
                        "-o",
                        wasm_tempfile ]
                log("Running: %s" % " ".join(cmd))
                subprocess.check_call(cmd)

                log("Starting interpreter for module '%s'" % wasm_tempfile)
                cmd = [opts.interpreter, "--repl", wasm_tempfile]
                log("Running: %s" % " ".join(cmd))
                r = Runner(cmd, no_pty=opts.no_pty)

                # Wait for the initial prompt
                try:
                    assert_prompt(r, ['webassembly> '], opts.start_timeout)
                except:
                    _, exc, _ = sys.exc_info()
                    log("\nException: %s" % repr(exc))
                    log("Output before exception:\n%s" % r.buf)
                    sys.exit(1)

            elif re.match("^\(assert_return\\b.*", form):
                #log("%s" % form)
                test_assert_return(r, opts, form)
            elif re.match("^\(assert_trap\\b.*", form):
                #log("%s" % form)
                test_assert_trap(r, opts, form)
            elif re.match("^\(invoke\\b.*", form):
                do_invoke(r, opts, form)
            elif re.match("^\(assert_invalid\\b.*", form):
                #log("ignoring assert_invalid")
                pass
            else:
                raise Exception("unrecognized form '%s...'" % form[0:40])
    finally:
        if not opts.no_cleanup:
            log("Removing tempfiles")
            os.remove(wast_tempfile)
            os.remove(wasm_tempfile)
        else:
            log("Leaving tempfiles: %s" % (
                [wast_tempfile, wasm_tempfile]))
