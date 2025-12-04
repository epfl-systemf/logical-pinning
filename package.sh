#!/usr/bin/env sh
rm -f logical-pinning.zip
git ls-files --recurse-submodules | \
    grep -v '^[.]git' | \
    zip -q logical-pinning.zip -@
