# FFPL 2023 Coq Material

This is the Coq material for FFPL 2023 taught at ETH Zurich by Ralf Jung and TA'd by Max Vistrup.
If you have any questions, please do not hesitate to raise a question on Moodle or contact the TA or lecturer.

If you are taking the course, make sure you are enrolled in [Moodle](https://moodle-app2.let.ethz.ch/course/view.php?id=20846)!
All official communication will be via Moodle.

## Fetching the material

The easiest way to fetch the material is via `git`.
If you already have git installed, simply find a suitable location on your file system and run:
```
git clone https://gitlab.inf.ethz.ch/public-plf/ffpl-2023.git
```

To install `git`:
- On Linux, `git` should be easy to install via your package manager.
- On macOS, `git` should come pre-installed and can be activated with `git version`.
- On Windows, you can install [Git for Windows](https://gitforwindows.org/).

Ideally you will never change one of the files we provide;
instead, you can make a copy and put your answers to the exercises (and your own experiments) there.
That way, `git pull` should always work to fetch the latest versions of the files.
If you change one of our files, you might have to resolve conflicts.

Alternatively, you can download the entire material folder as [a zip file][zip].
However, note that we will change and extend the material during the course, so you will have to re-download regularly.

[zip]: https://gitlab.inf.ethz.ch/public-plf/ffpl-2023/-/archive/master/ffpl-2023-master.zip

## Installing Coq

We recommend that you install Coq using the Coq Platform, [**version 2022.09.1**](https://github.com/coq/platform/releases/tag/2022.09.1).
(A new version 2023.03 is about to be released. We have not tested that version!)
You should then be able to view, edit, and compile Coq code using the CoqIDE program.
OS-specific instructions are given below.

### Linux

For Linux, we recommend you install Coq through the [Coq Platform Snap package](https://snapcraft.io/coq-prover).
The command for that is `sudo snap install coq-prover --channel=2022.09/stable`.
See [the official Linux installation instructions](https://github.com/coq/platform/blob/2022.09.1/doc/README_Linux.md) for further details.

<details><summary>Alternative installation instructions via opam</summary>

Alternatively, you can install Coq and the required dependencies through `opam`.
However, we will only be able to provide help if you follow the recommended instructions and use the Snap package.

But if you really want to not use Snap, then you can install opam (via your package manager or the [official release](https://opam.ocaml.org/doc/Install.html)), and then run the following commands in this folder:
```
make builddep
opam install coqide
```

</details>

### Mac OS

The installer for Coq platform for Mac OS can be found [here](https://github.com/coq/platform/releases/tag/2022.09.1).

Make sure you download the DMG image corresponding to your processor. Then, you should open the image and
(1) copy the `Coq-Platform~8.17~2023.08` to `Applications`,
(2) copy `coq-shell~8.17~2023.08.command` to `Desktop`.
As explained below, you must run `make` to build Coq files in the shell provided by opening `coq-shell~8.17~2023.08.command`.
Namely, this shell has all the necessary environment variables set.

(See also the [official macOS installation instructions](https://github.com/coq/platform/blob/2022.09.1/doc/README_macOS.md).)

### Windows

The installation for Windows is slightly more involved.
First, you have to run the Coq Platform Windows installer, which can be found [here](https://github.com/coq/platform/releases/tag/2022.09.1).
Please also see the [official Windows installation instructions](https://github.com/coq/platform/blob/2022.09.1/doc/README_Windows.md).

Next, download the [`gnumake` add-on](https://github.com/coq/platform/releases/download/2022.09.1/AddOn_gnumake_win64.zip) and extract it.
From this add-on, you should:

- Copy `gnumake.exe` to `C:\Coq-Platform~8.16~2022.09\bin`
- Copy `CoqMakefile.in` to `C:\Coq-Platform~8.16~2022.09\lib\coq-core\tools`

## Building the files

When one Coq file imports another, the imported file needs to be built first.
Unfortunately CoqIDE does not support automatically building imported files, so you will have to do this by hand.
To do this, you need to first open a Coq shell.

### Opening the Coq shell
[coq-shell]: #opening-the-coq-shell

The Coq shell is a terminal window for which all the necessary environment variables are set.
In particular, it lets you use the command `coqc`, which in turn is needed by our `Makefile`.
To open the Coq shell, do the following:

- On Linux, `eval $(coq-prover.env)` turns your current terminal into a Coq shell.
- On macOS, the package contains a `coq-shell[...].command` that you can open.
- On Windows, "Coq-Shell" should appear in your start menu.

### Running Make

Then, inside the Coq shell, navigate to the folder where you fetched the course material, and run `make` (on Windows: `gnumake`).

If you edit a file that is imported elsewhere, remember to re-run `make`/`gnumake` so that your changes can be imported.

## Working with the Coq code

To work on the Coq code, we recommend you use CoqIDE.
Other IDEs exist (there is the ProofGeneral plugin for emacs, and for vscode there are two extensions: vscoq and coq-lsp).
However, CoqIDE is what we will demonstrate in the course, and your lecturer and TA will not be familiar with all other IDEs.

CoqIDE should have been installed together with Coq if you followed our instructions.
On Linux and macOS, you can run `coqide` from the [Coq shell][coq-shell].
On Windows, "CoqIDE" appears in the start menu.

Launch CoqIDE, and open the first file: `theories/coq_warmup/part1.v`.
Press the toolbar button with an arrow that points to a horizontal line ("run to end") -- all the text should turn green, that indicates everything is working.
Navigate somewhere in the file and hit "Ctrl-Right" ("run to cursor"), and the green region should end near your cursor.
You can now navigate Coq files and are ready for the class!

## Source material

We stand on the shoulders of giants!
The material in this folder is based on two prior courses:
- "Program verification with types and logic" at Radboud University Nijmegen.
  Lecturer: Robbert Krebbers. TA: Jules Jacobs.
- "Semantics" at Saarland University.
  Lecturer: Derek Dreyer. TAs: Simon Spies, Lennard Gäher.
