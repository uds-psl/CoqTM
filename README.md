# Verified Programming of Turing Machines in Coq


Maximilian Wuttke's Bachelor's Thesis at the [Programming Sytems Lab](http://www.ps.uni-saarland.de/) at [Saarland University](https://www.uni-saarland.de/en/home.html).

The project's home page is [https://www.ps.uni-saarland.de/~wuttke/bachelor.php](here).

The online CoqDoc can be found [https://www.ps.uni-saarland.de/~wuttke/bachelor/coqdoc/toc.html](here).


## Compilation

[Coq](https://coq.inria.fr/) 8.7 or 8.8 is required.

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

The definitions of tapes and multi-tape Turing machines from Asperti, Riciotti ["A formalization of multi-tape Turing machines"](http://www.cs.unibo.it/~ricciott/PAPERS/multi_turing.pdf) (2015) and the accompanying Matita mechanisation.
Please also read the Acknowledgements section inside the thesis.

## Libraries

This project uses two libraries:

- Base Library:  Coq library for finite types, retracts, and inhabited types 
- smpl: A Coq plugin providing an extensible tactic similar to first.

Please consult the README files in the corresponding repos; the links are found under `externals/`.

We use [CoqDocJS](https://github.com/tebbi/coqdocjs) to make the CoqDoc code a bit fancier.


## Thesis

The source code of the thesis is found inside `tex/thesis`. It can be built using `make`.


## License

The source code is Copyright(c) 2017-2018 Maximilian Wuttke. It is licensed under the [MIT License](LICENSE).

All other files (including the thesis and its source code) are Copyright(c) 2017-2018 Maximilian Wuttke.
