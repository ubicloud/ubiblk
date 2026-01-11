# Third-Party Notices

This project uses third-party dependencies, each with their own license terms. This file contains the full license texts for dependencies that are bundled or closely integrated with ubiblk.

## Runtime Dependencies

### isa-l_crypto

**Project**: Intel Intelligent Storage Acceleration Library - Crypto Version  
**Repository**: https://github.com/intel/isa-l_crypto  
**Version**: v2.25.0 (and others as specified in builds)  
**License**: BSD-3-Clause  

```
Copyright(c) 2011-2024 Intel Corporation All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
  * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
  * Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in
    the documentation and/or other materials provided with the
    distribution.
  * Neither the name of Intel Corporation nor the names of its
    contributors may be used to endorse or promote products derived
    from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

SPDX-License-Identifier: BSD-3-Clause
```

### libblkio

**Project**: libblkio - Block device I/O library  
**Repository**: https://gitlab.com/libblkio/libblkio  
**License**: LGPL-2.1-or-later with some Apache-2.0 components  

**Note**: libblkio is licensed under the GNU Lesser General Public License v2.1 or later. Some components may be under Apache License 2.0. Please refer to the upstream repository at https://gitlab.com/libblkio/libblkio for the complete and up-to-date license information.

The prebuilt artifacts include the full license texts in the `LICENSES/` directory.

#### GNU Lesser General Public License v2.1 (Summary)

The full LGPL-2.1 license text can be found at: https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

libblkio is free software; you can redistribute it and/or modify it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation; either version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.

## Rust Dependencies

This project also uses numerous Rust crates, each with their own licenses. Run `cargo tree --prefix none --format "{p} {l}"` to see a complete list of Rust dependencies and their licenses. Common licenses include:

- Apache-2.0
- MIT
- Apache-2.0 OR MIT
- BSD-3-Clause
- MPL-2.0

For the exact versions and licenses of Rust dependencies, refer to `Cargo.lock` in the repository.

## Prebuilt Binary Artifacts

When using prebuilt binary artifacts (see [docs/deps-prebuilt.md](docs/deps-prebuilt.md)), the full license texts for isa-l_crypto and libblkio are included in each artifact under the `LICENSES/` directory.

To extract and view licenses from an artifact:

```bash
tar -I zstd -xf isa-l_crypto-v2.25.0-ubuntu22.04-baseline-x86_64.tar.zst LICENSES/
cat LICENSES/isa-l_crypto-LICENSE.txt
```

## Build-Time Dependencies

Build-time tools and dependencies (autoconf, meson, compilers, etc.) each have their own licenses but are not distributed with ubiblk binaries.

## Questions

For questions about third-party licenses or attribution, please open an issue at: https://github.com/ubicloud/ubiblk/issues
