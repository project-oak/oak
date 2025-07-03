# Using JJ

## Install jj

For googlers: http://go/jj-install .

## Set Up

In your existing git repo, run the following to initialize jj. This is non
destructive and can live alongside your existing git setup.

```console
jj git init --git-repo .
```

Tell `jj` to track the remote `main` branch when syncing:

```console
jj bookmark track main@origin
```

Run the following to see the latest commits:

```console
$ jj log
@  nknvyqkv tiziano88@gmail.com 2025-07-02 23:05:18.000 +01:00 49e124ea
│  (no description set)
◉  xkxnqpup ivanpetrov@google.com 2025-06-25 02:48:20.000 -07:00 main main@origin HEAD@git e097debc
╷  Connect the agent to a Rust MCP server
╷ ◉  vvqlovtx tiziano88@gmail.com 2025-06-24 22:48:47.000 +01:00 tzn_mac_shell_gemini d1b0faaa
╭─╯  Mac shell with Gemini
◉  rwyqsvyz tbinder@google.com 2025-06-17 00:44:55.000 -07:00 ef4fc17b
╷  Return endorsement claims as part of EndorsementDetails.
╷ ◉  otpppwyk jibbl@google.com 2024-08-06 00:11:55.000 +00:00 oak-on-prem@origin f021cdb7
╷ │  Remove the kv-server systemd entry, it will now be run via container.
╷ ◉  lyxmqmwp dingelish@google.com 2024-06-14 14:31:02.000 -07:00 602cbad0
╭─┤  (empty) Merge branch 'main' into oak-on-prem
◉ │  zspzvkxm dingelish@google.com 2024-06-14 11:57:44.000 -07:00 adc4e15c
╷ │  copy the vanilla kernel image to the target dir
╷ ◉  onwtospu dingelish@google.com 2024-06-13 14:31:14.000 -07:00 4cc29197
╭─┤  Merge branch 'main' into oak-on-prem
◉ │  ylssvzmk dingelish@google.com 2024-06-13 20:45:08.000 +00:00 d34d074e
╷ │  explain the error of missing vhost_vsock kmod
╷ ◉  zvzuknuo dingelish@google.com 2024-06-13 14:04:07.000 -07:00 48bbb1f7
╷ │  Revert two changes
╷ ◉  lwswwltw dingelish@google.com 2024-05-30 17:06:42.000 -07:00 868ed884
╷ │  Enable SEV-SNP in oak_containers_launcher
╷ ◉  omospklw dingelish@google.com 2024-05-30 16:48:14.000 -07:00 4d5219a2
╷ │  force the type_of_loader to 0xFF
╷ ◉  wqnuzwrk dingelish@google.com 2024-05-29 17:27:32.000 +00:00 d922b431
╷ │  remove an unused flag for cloud-hypervisor
```

## Gerrit utils

Append the following to your global config.

```console
jj config edit --user
```

```toml
[aliases]
cr = ["util", "exec", "--", "bash", "-c", """
set -euo pipefail
INPUT=${1:-"@-"}
HASH=$(jj log --revisions="${INPUT}" --template=commit_id --no-graph)
HASHINFO=$(git log --max-count=1 ${HASH} --oneline --color=always)
echo "Pushing from commit ${HASHINFO}"
git push origin "${HASH}":refs/for/main
""", ""]
```

Append the following to your repo-specific config (since you most likely don't
want to add gerrit-style change-id headers to all your other repos).

```console
jj config edit --repo
```

```toml
[templates]
commit_trailers = '''
if(self.author().email() == "YOUR_EMAIL_HERE" &&
  !trailers.contains_key("Change-Id"),
  format_gerrit_change_id_trailer(self)
)
'''
```

## First commit

Start a new change, branching from `main`:

```console
jj new main
```

Make changes to some file, e.g.:

```console
vim README.md
```

Commit the change and provide a description.

```console
jj commit
```

Then enter something like "test change".

Confirm the change shows up correctly. Note that you will now be in a new empty
change (identified by the `@` symbol). The commit you just finished is the one
before that, which is also referred to as `@-` (which is why the `cr` alias we
added above refers to that by default, although you can override it by
specifying a different one).

```console
$ jj log
@  yyzkwmuk tzn@google.com 2025-07-03 23:44:35 67e7c31c
│  (empty) (no description set)
○  nknvyqkv tzn@google.com 2025-07-03 23:44:35 git_head() 4aa996b2
│  test change
│ ○  vpqyvtyn tzn@google.com 2025-07-03 22:33:58 7dc69c3d
├─╯  (no description set)
◆  xkxnqpup ivanpetrov@google.com 2025-06-25 10:48:20 main main@origin e097debc
│  Connect the agent to a Rust MCP server
~  (elided revisions)
│ ○  vvqlovtx tiziano88@gmail.com 2025-06-24 22:48:47 tzn_mac_shell_gemini d1b0faaa
├─╯  Mac shell with Gemini
◆  rwyqsvyz tbinder@google.com 2025-06-17 08:44:55 ef4fc17b
│  Return endorsement claims as part of EndorsementDetails.
~
```

## Addressing comments

Once comments are received on the CR, apply any changes locally to a new change
on top of the one that was just pushed. Once you are happy with the changes, run

```console
jj diff
```

to confirm the changes look as expected, and if so then run

```console
jj squash
```

which will move them to the parent change (the one we just pushed upstream). At
this point, you can push the updated version of that change to Gerrit again with

```console
jj cr
```

## Rebasing

If new changes are pushed upstream and you want to rebase your current change on
top of that, you can run the following command:

```console
jj git fetch --all-remotes
```

You can also turn this into an alias in `jj config edit --user`:

```toml
[aliases]
sync = ['git', 'fetch', '--all-remotes']
```

If you run `jj log` now, you will see that your current change still branches
from the original commit from which it was created:

```console
$ jj log
❯ jj
@  nxsutwpm tzn@google.com 2025-07-09 17:53:48 4c7af7cc
│  (no description set)
○  vmznqvzn tzn@google.com 2025-07-09 17:53:48 git_head() e2f45c58
│  (no description set)
○  nknvyqkv tzn@google.com 2025-07-09 17:53:48 a8d8baf5
│  Add instructions on how to use `jj`
│ ◆  kuompkru jibbl@google.com 2025-07-09 17:25:12 main 35746f5f
│ │  Remove deprecated constructor functions
│ ~  (elided revisions)
├─╯
│ ○  wqzmptzt tzn@google.com 2025-07-08 17:04:32 f624b680
├─╯  Update MCP documentation
◆  woxrsqsy albgonz@google.com 2025-07-08 16:28:23 8cb0682f
│  Add functionality to export server attestation evidence.
```

To rebase it on top of the newly synced main, you can run

```console
jj rebase --destination=main
```

This is also worth an alias for convenience:

```toml
[aliases]
evolve = ['rebase', '--destination=main']
```

If there are no conflicts, your change now has the current upstream main as its
parent.

If there are conflicts, you need to resolve them.

See https://github.com/jj-vcs/jj/blob/main/docs/conflicts.md for more details.

## References

- https://steveklabnik.github.io/jujutsu-tutorial/real-world-workflows/the-squash-workflow.html
- https://steveklabnik.github.io/jujutsu-tutorial/sharing-code/gerrit.html
