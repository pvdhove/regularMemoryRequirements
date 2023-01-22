# Chromatic memory requirements of regular reachability and safety objectives

This repository contains methods to compute minimal (i.e., with as few states as possible) automatic memory structures that contain sufficient information in order to play optimally in two-player zero-sum turn-based games on graphs for some specific objectives.
These objectives are *regular reachability* and *regular safety* objectives, i.e., objectives recognizable by reachability or safety automata.
Equivalently, they are the omega-regular objectives that are open or closed in the Borel hierarchy.
Technical details and proofs related to this repository can be found in [the paper](https://arxiv.org/abs/2210.09703).

# Requirements

- This repository uses Python 3. We assume that `pip` is installed in order to install Python packages ([installation instructions](https://pip.pypa.io/en/stable/installation/)).
The two Python packages that we use can be installed with `python3 -m pip install -r requirements.txt`; on Windows, you might have to replace `python3` with `py`.
The two packages are:
  - [automata-lib](https://pypi.org/project/automata-lib/) is used to manipulate automata and regular expressions (can be installed separately with `python3 -m pip install automata-lib`).
  - [PySAT](https://pysathq.github.io/) is used to get access to a range of SAT solvers to solve our NP-complete problems (can be installed separately with `python3 -m pip install python-sat`).
- To visualize the automata, Graphviz must also be installed (`sudo apt install graphviz` on Ubuntu, and we refer to the [installation page](https://graphviz.org/download/) for other systems; program `dot` should be added to the PATH after the installation).
- Examples can be run and visualized with `jupyter notebook` (can be installed with `python3 -m pip install notebook`; check the warnings as program `jupyter` may not be on the PATH after this; with Ubuntu, it is in `~/.local/bin/jupyter`).

# Usage

The main code that computes memory requirements is in `memReq.py`.
There are three Jupyter notebooks illustrating its use: `examplesSafety.ipynb` focuses on computing memory requirements of regular safety objectives, `examplesReachability.ipynb` focuses on computing memory requirements of regular reachability objectives, and `fromRegex.ipynb` shows how to compute the memory requirements of objectives specified as regular expressions.
The first two notebooks cover all the regular examples from the paper (and generalizations thereof).
The third one makes it easy to try other objectives by changing the regular expressions.

