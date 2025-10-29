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
3. Run the test suite:
   ```bash
   cargo test
   ```
