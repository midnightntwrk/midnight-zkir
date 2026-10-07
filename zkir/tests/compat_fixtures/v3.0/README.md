Frozen ZKIR 3.0 baseline. Every file here (`.zkir`, `.bzkir`, and the key
hashes in `keys.sha256`) was produced by the `midnight-zkir-v3` 3.0.0-rc.2
release binary, the version the Compact compiler pins. `all_instructions.zkir`
uses every 3.0 instruction and type; the `compact_*` files are real output of
the 3.0 Compact compiler.

Never regenerate or edit these files: they pin what 3.0 wrote, not what the
current code writes. A later release gets its own directory.
