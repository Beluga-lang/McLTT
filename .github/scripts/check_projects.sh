#!/bin/bash

dir=${1?directory unspecified}

function error_out () {

    echo "$1 is not in the _CoqProject file" >&2
    exit 1
}

cd "${dir}"

for f in *.v; do
    grep -q -F "${f}" _CoqProject || error_out "${f}"
done

exit 0
