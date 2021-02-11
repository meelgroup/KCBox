# KCBox

KCBox is a long-term project that aims at developping an open-source toolkit for knowledge compilation (KC) and KC-related reasoning tasks. So far, we have released three tools: PreLite, Panini, and ExactMC.
The following researchers have contributed to this project (sorted alphabetically by last name): 

- Yong Lai
- Dayou Liu
- Kuldeep S. Meel
- Roland H. C. Yap
- Minghao Yin

<!-- ####################################################################### -->

## PreLite Description

PreLite is a light version of preprocessor that can simplify a CNF formula as an equivalent one. This tool was initiated by Yong Lai, Kuldeep S. Meel, and Roland H. C. Yap. 

## Panini Description

Panini is an efficient compiler. So far, it suppots the compilation from CNF formula to OBDD or OBDD\[$\wedge$\]. This tool was initiated by Yong Lai, Dayou Liu, and Minghao Yin. Later, it was deeply optimized when Yong Lai was in National University of Singapore with the help from Kuldeep S. Meel and Roland H. C. Yap. Kuldeep S. Meel named it as Panini (the name of an ancient linguist). If you use this tool, please cite our paper [New Canonical Representations by Augmenting OBDDs with Conjunctive Decomposition](https://dblp.org/rec/journals/jair/LaiLY17.html?view=bibtex)

## ExactMC Description

ExactMC is a scalable exact model counter. This tool was initiated by Yong Lai, Kuldeep S. Meel, and Roland H. C. Yap. It performs counting wrt a KC language called constrained conjunction \& decision diagrams that supports linear model counting. If you use this tool, please cite our paper "the power of literal equivalence in model counting"

<!-- ####################################################################### -->

## Installation

### Prerequisites
- cmake 
- g++ 
- make
- libraries:
   - zlib
   - gmp

### Commands

```
cd build 
./build.sh 
```

<!-- ####################################################################### -->

## Usage

### Using Binary

Use "KCBox --help" to see the usage of the toolkit, and "KCBox toolname --help" to see the options of a single tool.

### Precautions for Source Code

- Directory solvers contains some other tools that are used for debugging. If they does not work on your computer, please build them yourself.

<!-- ####################################################################### -->

## Acknowledgment

- Arijit Shaw
- Mate Soos

