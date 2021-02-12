# KCBox

KCBox is a long-term project that aims at developping an open-source toolkit for knowledge compilation (KC) and KC-related reasoning tasks. 
It should be emphasized that this projected is GPLv3 licensed.
So far, we have released three tools: PreLite, Panini, and ExactMC.
The following researchers have contributed to this project (sorted alphabetically by last name; see history.txt for a rough description): 

- Yong Lai
- Dayou Liu
- Kuldeep S. Meel
- Roland H. C. Yap
- Minghao Yin

<!-- ####################################################################### -->

## PreLite Description

PreLite is a light version of preprocessor that can simplify a CNF formula as an equivalent one. Since PreLite was used as the first kernelization in ExactMC, if you use this tool, please cite our paper [The power of Literal Equivalence in Model Counting](https://meelgroup.github.io/files/publications/AAAI-21-LMY.pdf)

## Panini Description

Panini is an efficient compiler. So far, it suppots the compilation from CNF formula to OBDD or OBDD\[$\wedge$\]. If you use this tool, please cite our paper [New Canonical Representations by Augmenting OBDDs with Conjunctive Decomposition](https://dblp.org/rec/journals/jair/LaiLY17.html?view=bibtex)

## ExactMC Description

ExactMC is a scalable exact model counter. This tool was initiated by Yong Lai, Kuldeep S. Meel, and Roland H. C. Yap. It performs counting wrt a KC language called constrained conjunction \& decision diagrams that supports linear model counting. If you use this tool, please cite our paper [The power of Literal Equivalence in Model Counting](https://meelgroup.github.io/files/publications/AAAI-21-LMY.pdf)

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

