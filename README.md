# KCBox

KCBox is a long-term project that aims at developping an open-source toolkit for knowledge compilation (KC) and KC-related reasoning tasks. 
It should be emphasized that this projected is GPLv3 licensed.
So far, we have released three tools: PreLite, Panini, and ExactMC.
The following researchers have contributed to this project (sorted alphabetically by last name; see history.txt for a simple description): 

- Yong Lai
- Dayou Liu
- Kuldeep S. Meel
- Roland H. C. Yap
- Minghao Yin

<!-- ####################################################################### -->

## PreLite Description

PreLite is a light version of preprocessor that can simplify a CNF formula in DIMACS format as an equivalent one. 
For example, (x1 or x2) and (not x1 or not x2 or not x3) can be expressed in DIMACS format as follows:

```
p cnf 3 2
1 2 0
-1 -2 -3 0
```

Since PreLite was designed for the first kernelization in ExactMC, if you use this tool, please cite our paper [The power of Literal Equivalence in Model Counting](https://meelgroup.github.io/files/publications/AAAI-21-LMY.pdf)

## Panini Description

Panini is an efficient compiler. So far, it suppots the compilation from CNF formula in DIMACS format to OBDD or OBDD\[$\wedge$\], which are the format of tractable circuits. If you use this tool, please cite our paper [New Canonical Representations by Augmenting OBDDs with Conjunctive Decomposition](https://dblp.org/rec/journals/jair/LaiLY17.html?view=bibtex)

## ExactMC Description

ExactMC is a scalable exact model counter. It performs counting wrt a KC language called constrained conjunction \& decision diagrams that supports linear model counting. This tool also takes in a CNF formula in DIMACS format, and outputs the number of satisfying assignments. If you use this tool, please cite our paper [The power of Literal Equivalence in Model Counting](https://meelgroup.github.io/files/publications/AAAI-21-LMY.pdf)

<!-- ####################################################################### -->

## Installation

### Prerequisites

```
sudo apt-get install build-essential cmake
sudo apt-get install zlib-devel
sudo apt-get install libgmp-dev
```

### Commands

```
mkdir build && cd build
cp ../scripts/build.sh .
chmod u+x build.sh
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

