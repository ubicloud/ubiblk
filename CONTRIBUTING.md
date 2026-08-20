# Contributing to ubiblk

Thanks for your interest in contributing to ubiblk! This document explains how to
contribute and the one requirement we ask of every contributor: signing our
Contributor License Agreement (CLA).

## Contributor License Agreement

Before we can merge your contribution, you must sign the Ubicloud Contributor
License Agreement. Signing is a one-time action, and the same signature covers
all Ubicloud projects that use this CLA (including ubicloud itself), so if you
have already signed it elsewhere you are all set.

When you open your first pull request, the CLA Assistant bot comments on it with
a link to the CLA and instructions. To sign:

1. Read the [CLA document][cla].
2. Post this exact comment on your pull request:

   ```
   I have read the CLA Document and I hereby sign the CLA
   ```

The bot then records your signature in the [ubicloud/cla-signers][signers]
repository and marks the CLA status check as passed. If a later change makes the
bot ask again, comment `recheck` to re-run it.

Ubicloud employees and a small set of maintainers are exempt; they are listed in
the `allowlist` of [`.github/workflows/cla.yaml`](.github/workflows/cla.yaml).

## How to contribute

1. Fork the repository and create a branch for your change.
2. Make your change, keeping it focused and covered by tests where practical.
3. Run the checks locally (see [`.github/workflows/ci.yaml`](.github/workflows/ci.yaml)).
4. Open a pull request against `main` and sign the CLA as described above.

[cla]: https://docs.google.com/document/d/1ymjqOk6fXhi-VxnV2qZEgI5ibX9gtg7Y/edit?usp=sharing&ouid=105153831332304232521&rtpof=true&sd=true
[signers]: https://github.com/ubicloud/cla-signers
