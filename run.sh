#!/bin/bash
#motivation
motivation=$(pwd)"/motivation/moti0.unit"
num1=3
#frag 0-5 represent the six different groups of programs
combination=$(pwd)"/benchmark_combin/frag0/seq0/benchmark0.unit"
num2=1000
#mu 0-9 represent ten different groups of programs
regreaasion=$(pwd)"benchmark_stmt_mu/mu0/benchmark_mu0.unit"
num3=10
#sq 0-9 represent ten different orders of programs
order=$(pwd)"/benchmark_combin/frag0/seq0/benchmark0.unit"
num4=1000
#correct 0-100 represent six different proportion of correct programs
proportion=$(pwd)"/benchmark_combin/frag0/correct0/benchmark0.unit"
num5=500
#benchmark for the evaluation of the trace abstract method
gen=$(pwd)"/benchmark_fm/benchmark_unit/benchmark0.unit"
num6=50

./CollaV4UP/_build/default/main.exe -colla $1 -filename $motivation -num $num1

