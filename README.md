# CCS 2026 Artifact

The two main artefacts are:
- [`golgge`](./crates/golgge/) for the `golgge` backtracking engine. It is only a library.
- [`indistinguishability`](./crates/indistinguishability/) for the protocol verifier

The repository also includes [`cryptovampire`](./crates/cryptovampire/) from [1] vendored in for inspiration and its supporting crates as well as [`egg`](./crates/egg/) from [2]. 

## Building
### [`nix`](https://nixos.org/)
This is a `nix` enabled repository. So simply call `nix build` to make the binary available at `./result/bin/indistinguishability`.

### `cargo`
[`indistinguishability`](./crates/indistinguishability/) needs `rust` `nightly`. The experimiments were in particular ran according using [`rust 1.96.0`](./rust-toolchain.toml), but any sufficiently recent rust should work fine.

To compile [`indistinguishability`](./crates/indistinguishability/) simply run
```
cargo build --release
```
The binary should then be available at [`./target/release/indistinguishability`](./target/release/indistinguishability).

## Running
```bash
indistinguishability file.scm # runs a scheme file
indistinguishability # runs from stdin
indistinguishability -i # starts steel's repl mode for an interactive execution
indistinguishaility --help # for any other options
```
Note that all option can be overwritten by the scheme file. This is notably done in all examples for reproducibility.

### SMT solver
To run `indistinguishability` you need at least `vampire`, `z3` or `cvc5` available. `indistinguishability` will default to searching in you `PATH`, otherwise options can overwrite this.

Once again the `nix` shell provides these solvers using the exact version use to generate the table of the paper.

## Experiments
The experiments in the paper are in [`./crates/indistinguishability/tests/passing/`](./crates/indistinguishability/tests/passing/README.md). Refer to the [`README.md`](./crates/indistinguishability/tests/passing/README.md) there for more informations.

## Refrences

[1] Jeanteur, Simon, et al. "CryptoVampire: Automated reasoning for the complete symbolic attacker cryptographic model." 2024 IEEE Symposium on Security and Privacy (SP). IEEE, 2024.

[2] Willsey, Max, et al. "Egg: Fast and extensible equality saturation." Proceedings of the ACM on Programming Languages 5.POPL (2021): 1-29.