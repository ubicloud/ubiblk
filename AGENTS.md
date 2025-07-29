# Repository Contribution Guidelines

This repo contains Rust code. Before submitting changes:

1. Format the code:
   ```bash
   cargo fmt --all -- --check
   ```
2. Run the linter:
   ```bash
   cargo clippy --all-targets --all-features -- -D warnings
   ```
3. Run the test suite with and without the optional `isa-l_crypto` dependency:
   ```bash
   cargo test
   cargo test --features disable-isal-crypto
   ```
