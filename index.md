## Goal

This project builds a basic proof assistant which is able to reason on proof modules from a decentralized network of containers. The reason we want decentralization of Coq modules instead of storing them on a centralized site like GitHub is because some of these Coq modules may contain knowledge graph information which users want to own privately and protect with access control. 

It will save modules on [Solid](https://solidproject.org/) and use Coq as the type engine. The controller will be Julia because of the speed of compiled programs and the flexibility to write macros. We are also using Julia because there are some cool category theory projects (CatLab for instance) in Julia. Julia will play the role of the proof assistant, manipulating terms and calling Coq for type-checking. As the user interface, we will be using Jupyter Notebook as an interactive platform, rather than our own interactive website. In future, we will build other backends to replace Solid and Coq, and also develop frontends beyond Julia and Jupyter.

## Setup

### Windows

WSL2 is a stable virtual environment developed for Windows that lets us develop software in a Linux system. Here are some suggestions for getting started.

1. WSL2
   - [Uninstall](https://pureinfotech.com/uninstall-wsl2-windows-10/) old versions of WSL.
   - [Install](https://docs.microsoft.com/en-us/windows/wsl/install-win10) new version of WSL2.
2. Ubuntu
   - Install and launch Ubuntu 20.04 via Windows Store.
   - Set username and password.
   - Update Ubuntu.
     ```
     sudo apt update && sudo apt upgrade && sudo apt autoremove -y
     ```
3. Terminal
   - Install and launch Windows Terminal via Windows Store.
   - Set Ubuntu as default profile.
   - [Change](https://docs.microsoft.com/en-us/windows/terminal/troubleshooting) default working directory for Ubuntu.
4. XWindows
   - [Install](https://github.com/affeldt-aist/mathcomp-install/blob/master/install-windows-en.org) vcxsrv.
   - Save config to desktop for easy launch.
   - Test vcxsrv. 
     ```
     sudo apt-get install -y x11-apps
     
     xeyes
     ```
   - In future, Microsoft may release WSLg.
5. Git and VSCode
   - Already installed in WSL2.
   - [Set up](https://docs.microsoft.com/en-us/windows/wsl/tutorials/wsl-git) config file and credentials manager.
   - [Clone](https://git-scm.com/book/en/v2/Git-Basics-Getting-a-Git-Repository) your repository inside your projects folder.
6. VS Code
   - [Install](https://code.visualstudio.com/download) VS Code.
   - [Install](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-wsl) Remote - WSL extension.
   - [Initialize](https://code.visualstudio.com/blogs/2019/09/03/wsl2) VS Code inside your repository folder.

## Installation

1. Jupyter
   - [Install](https://towardsdatascience.com/configuring-jupyter-notebook-in-windows-subsystem-linux-wsl2-c757893e9d69) Miniconda.
2. Julia
   - [Install](https://ferrolho.github.io/blog/2019-01-26/how-to-install-julia-on-ubuntu) Julia binaries.
3. Add Julia to Jupyter
   - [Install](https://datatofish.com/add-julia-to-jupyter/) IJulia.
4. OPAM
   - [Install](https://github.com/affeldt-aist/mathcomp-install/blob/master/install-windows-en.org) OPAM.
   - [Say](http://ace.cs.ohio.edu/~gstewart/courses/4100-16/hw/0.html) yes to modifying profile and adding hook during ``opam init``.
   - [Run](https://ocaml.org/docs/install.html) ``eval $(opam env)`` after every ``opam`` command (for Coq, CoqIDE, MathComp too).
5. Coq
   - [Install](https://coq.inria.fr/opam-using.html) Coq.
   - Note that ``opam-depext`` needs to be installed and run first.
6. CoqIDE
   - [Install](https://coq.inria.fr/opam-using.html) CoqIDE.
   - Note that ``opam-depext`` needs to be run first.
   - Install ``gnome-icon-theme`` for CoqIDE icons.
     ```
     sudo apt-get install -y gnome-icon-theme
     ```
7. MathComp
   - [Install](https://coq.inria.fr/opam-using.html) MathComp.
8. VSCoq
   - A good alternative to CoqIDE.
   - Run ``code .`` from any WSL2 folder.
   - [Install](https://github.com/coq-community/vscoq) VSCoq extension in VS Code.
   - Specify the path to coqtop, e.g.
     ```
     "coqtop.binPath": "/home/<username>/.opam/4.12.0/bin/"
     ```
   - Restart VS Code for changes to take effect.
9. Node.js
   -[Install](https://github.com/nvm-sh/nvm#install--update-script) nvm.
   -[Install](https://github.com/nvm-sh/nvm#usage) node using nvm.
10. Solid-shell
   -[Install](https://www.npmjs.com/package/solid-shell) sol globally
     ```
     npm install -g solid-shell
     ```   

## Experiments

### 20210427-solid-access

   - I like Julia's project environment management system. 
   - To use it, first navigate to the project directory. 
   - Launch the Julia REPL.
   - Start the package mode by typing ``]``.
   - Generate the project environment.
     ```
     activate .
     ```
   - Install the following packages required for the experiment.
     ```
     add HTTP JSON PyCall
     ```
   - Exit the Julia REPL.
   - Start Jupyter Notebook in the project directory.
   - The project environment is activated when Jupyter loads.
   - Load the file "20210427-solid-access.ipynb" from the experiments folder.

   
