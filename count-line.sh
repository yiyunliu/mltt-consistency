#!/usr/bin/env sh
# Count line numbers using the tokei utility
# Note that the output includes the syntactic soundness proof, which
# is independent of the semantic soundness proof presented in the text
tokei -f theories/*.v
