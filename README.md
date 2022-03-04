# Collaborative-Verification-for-UP

## 1、Installation

- recommand OS: **Ubuntu 18.04**
- ocaml 4.11.1
- dune 2.7.1

## 2、Benchmark

|--**Collaborative-Verification-for-UP**

​			|-- **benchmark_stmt_mu** 

​							|-- **mu0 - mu9**  - ten different groups of programs obtained by mutation

​			|-- **benchmark_combin** 

​							|-- **frag0 - frag5**  - six different groups of programs obtained by combination

​									|-- **seq0**  -  current group of programs

​									|-- **seq0 - seq9**  - ten different orders of the current group of programs

​									|-- **correct0 - correct100**  -  different proportion of correct programs

​               

## 3、Usage

```
cd  $ROOT/Collaborative-Verification-for-UP/CollaV4UP

dune  build main.exe

./_build/default/main.exe  -colla [true/false]  -filename  [file address]   -num [program nums]
```



***-colla***     collaborative version (true)  or  non-collaborative version (false)

***-filename***    the file address for verified programs

***-num***    the number for verified programs

For example,  moti0.unit - moti2.unit are be collaborative verified.

`./_build/default/main.exe  -colla true  -filename  $root/moti0.unit   -num 3`

**Results**

```
`--------------------------------------------demo0---------------------------------`
`refindment nums:2`
`verify_time: 0.004991`
`demo0 is ******correct`
`--------------------------------------------demo1---------------------------------`
`refindment nums:1`
`verify_time: 0.000279`
`demo1 is ******correct`
`--------------------------------------------demo2---------------------------------`
`refindment nums:0`
`verify_time: 0.000181`
`demo2 is ******correct`
`########################################################`
`runtime:0.005479`
```

***refindment nums*:** the number of iterations of CEGAR

***verify_time*:**  time cost for program verification

***correct/incorrect*:** result for program verification

***runtime:***  total time cost for programs verification

## 4、Experiment

```
./run.sh  [true/false]
```

[true/false]:  collaborative version (true)  or  non-collaborative version (false)

We set up the file to run the motivation example. You can modify the code for different benchmarks. 

You can refer to [Verifier4UP](https://github.com/Verifier4UP/Trace-Refinement-based-Verification) for the effectiveness evaluation of Trace abstraction.

