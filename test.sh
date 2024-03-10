#!/bin/bash
benchmark="_synth_sizedlist"
number=2
#dune exec -- bin/main.exe coverage-type-check meta-config.json
#data/benchmark/quickchick/${benchmark}/${number}/prog.ml
#data/benchmark/quickchick/${benchmark}/_under.ml

dune exec -- bin/main.exe coverage-type-check meta-config.json data/benchmark/quickchick/sortedlist/prog.ml data/benchmark/quickchick/sortedlist/_under.ml

#dune exec -- bin/main.exe coverage-type-check meta-config.json data/benchmark/quickchick/sizedlist/prog.ml data/benchmark/quickchick/sizedlist/_under.ml