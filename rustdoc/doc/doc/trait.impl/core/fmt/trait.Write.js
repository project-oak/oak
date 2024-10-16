(function() {
    var implementors = Object.fromEntries([["oak_restricted_kernel_sdk",[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Write.html\" title=\"trait core::fmt::Write\">Write</a> for <a class=\"struct\" href=\"oak_restricted_kernel_sdk/utils/struct.Stderr.html\" title=\"struct oak_restricted_kernel_sdk::utils::Stderr\">Stderr</a>"]]],["sev_serial",[["impl&lt;F, R, W&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Write.html\" title=\"trait core::fmt::Write\">Write</a> for <a class=\"struct\" href=\"sev_serial/struct.SerialPort.html\" title=\"struct sev_serial::SerialPort\">SerialPort</a>&lt;F, R, W&gt;<div class=\"where\">where\n    F: IoPortFactory&lt;'static, <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>, R, W&gt;,\n    R: PortReader&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt; + 'static,\n    W: PortWriter&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt; + 'static,</div>"]]]]);
    if (window.register_implementors) {
        window.register_implementors(implementors);
    } else {
        window.pending_implementors = implementors;
    }
})()
//{"start":57,"fragment_lengths":[324,745]}