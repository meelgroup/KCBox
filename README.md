# KCBox

KCBox is a long-term project that aims at developping an open-source toolbox for knowledge compilation (KC) and KC-related reasoning tasks. 
So far, we have released four tools: PreLite, Panini, ExactMC, and PartialKC.

<!-- ####################################################################### -->

## PreLite Description

PreLite is a light version of preprocessor that can simplify a CNF formula in DIMACS format as an equivalent one, and therefore can work with knowledge compilers, such as c2d and D4.
For example, (x1 or x2) and (not x1 or not x2 or not x3) can be expressed in DIMACS format as follows:

```
p cnf 3 2
1 2 0
-1 -2 -3 0
```

Since PreLite was designed for the first kernelization in ExactMC, if you use this tool, please cite our paper [The power of Literal Equivalence in Model Counting](https://meelgroup.github.io/files/publications/AAAI-21-LMY.pdf)

## Panini Description

Panini is an efficient compiler. So far, it suppots the compilation from CNF formula in DIMACS format to OBDD, OBDD\[AND\] (OBDD with conjunctive decomposition), or CCDD (constrained conjunction \& decision diagrams ) which are the format of tractable circuits. If you use this tool to compile formula into OBDD or OBDD\[AND\] , please cite our paper [New Canonical Representations by Augmenting OBDDs with Conjunctive Decomposition](https://dblp.org/rec/journals/jair/LaiLY17.html?view=bibtex). If you use this tool to compile formula into CCDD, please cite our paper [CCDD: A Tractable Representation for Model Counting and Uniform Sampling](https://arxiv.org/abs/2202.10025)

## ExactMC Description

ExactMC is a scalable exact model counter. It performs counting wrt CCDD that supports linear model counting. This tool also takes in a CNF formula in DIMACS format, and outputs the number of satisfying assignments. ExactMC also supports weighted model counting by searching wrt Decision-DNNF under the format of [MC competition](https://mccompetition.org/). If you use this tool, please cite our paper [The power of Literal Equivalence in Model Counting](https://meelgroup.github.io/files/publications/AAAI-21-LMY.pdf)

## ExactUS Description

ExactUS is an exactly uniform sampler. The main idea is to first compile the formula into CCDD and then sample wrt the compilation. This tool also takes in a CNF formula in DIMACS format, and outputs a given number of random solutions. If you use this tool, please cite our paper [CCDD: A Tractable Representation for Model Counting and Uniform Sampling](https://arxiv.org/abs/2202.10025)

## PartialKC Description

PartialKC is an anytime model counter with fast convergence performance. The main idea is to perform partial knowledge compilation wrt a KC language called partial constrained conjunction \& decision diagrams. This tool also takes in a CNF formula in DIMACS format, and outputs an estimate of its true model count. If you use this tool, please cite our paper "Fast Converging Anytime Model Counting"

<!-- ####################################################################### -->

## Installation

### Prerequisites

```
sudo apt-get install build-essential cmake
sudo apt-get install zlib1g.dev
sudo apt-get install libgmp-dev
```

### Commands

```
mkdir build && cd build
cp ../scripts/build.sh .
chmod u+x build.sh
./build.sh  ## if you want to build a single tool, please use "./build.sh toolname" instead
```

<!-- ####################################################################### -->

## Usage

### Using Binary

Use "KCBox --help" to see the usage of the toolkit, and "KCBox toolname --help" to see the options of a single tool.

### Precautions for Source Code

- Directory solvers contains some other tools that are used for debugging. If they do not work on your computer, please build them yourself.

<!-- ####################################################################### -->

## Contributors

The following researchers have contributed to this project (sorted alphabetically by last name; see history.txt for a rough description of contributions): 

- Yong Lai (laiy@jlu.edu.cn)
- Dayou Liu (dyliu@jlu.edu.cn)
- Kuldeep S. Meel (meel@comp.nus.edu.sg)
- Roland H. C. Yap (ryap@comp.nus.edu.sg)
- Minghao Yin (ymh@nenu.edu.cn)

<!-- ####################################################################### -->

## Acknowledgment

- Daniil Chivilikhin
- Arijit Shaw
- Mate Soos
- Suwei Yang
