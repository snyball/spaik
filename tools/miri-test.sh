#!/usr/bin/env bash

export MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-tree-borrows"
cargo miri test
