#!/usr/bin/env bash

# // TODO(#913): Implement introspection client

dir=./dist
mkdir -p $dir

indexjs=$dir/index.js
indexhtml=$dir/index.html

test -f $indexjs || touch $indexjs
test -f $indexhtml || touch $indexhtml
