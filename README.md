# Verified Programming of Turing Machines in Coq


Maximilian Wuttke's Bachelor's Thesis at the [Programming Sytems Lab](http://www.ps.uni-saarland.de/) at [Saarland University](https://www.uni-saarland.de/en/home.html).

The project's home page is [here](https://www.ps.uni-saarland.de/~wuttke/bachelor.php).
The online CoqDoc can be found [here](https://www.ps.uni-saarland.de/~wuttke/bachelor/coqdoc/toc.html).
The GitHub repo is [here](https://github.com/uds-psl/CoqTM).


## Compilation

[Coq](https://coq.inria.fr/) 8.7 or 8.8 or 8.9 is required.

Get the source code and the libraries via

	git clone https://github.com/mwuttke97/CoqTM
	cd CoqTM
	git submodule update --init --recursive

Compile the libraries:

	cd external/base && make -j
	cd ../smpl && make -j
	cd ../..

Note that if you have Coq 8.7, you need to execute `git checkout v8.7` inside `external/smpl`.
Compile the main source code:

	make -j

This should take ca. 5-10 minutes.

## Acknowledgements

The definitions of tapes and multi-tape Turing machines are taken from Asperti, Riciotti ["A formalization of multi-tape Turing machines"](http://www.cs.unibo.it/~ricciott/PAPERS/multi_turing.pdf) (2015) and the accompanying Matita mechanisation.

My advisor of this thesis, [Yannick Forster](https://www.ps.uni-saarland.de/~forster/), did the initial translation from Matita to Coq and implemented some prototypes.

Please also read the [Acknowledgements](tex/thesis/acknowledgements.tex) section of the thesis.

## Libraries

This project uses two libraries:

- Base Library:  Coq library for finite types, retracts, and inhabited types 
- smpl: A Coq plugin providing an extensible tactic similar to first.

Please consult the README files in the corresponding repos; the links are found under `externals/`.

We use [CoqDocJS](https://github.com/tebbi/coqdocjs) to make the CoqDoc code a bit fancier.


## Thesis

The source code of the thesis is located inside `tex/thesis`.
It can be built using `make`.

It can be downloaded from [here](https://www.ps.uni-saarland.de/~wuttke/bachelor/downloads/thesis.pdf).

## License

The source code is Copyright(c) 2017-2018 Maximilian Wuttke. It is licensed under the [MIT License](LICENSE).

All other files (including the thesis and its source code, but excluding the external libraries) are Copyright(c) 2017-2018 Maximilian Wuttke.
