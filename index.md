## Goal

This project builds a basic proof assistant which is able to reason on proof modules from a decentralized network of containers.

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

## Installation

1. Jupyter
   - [Install](https://towardsdatascience.com/configuring-jupyter-notebook-in-windows-subsystem-linux-wsl2-c757893e9d69) Miniconda.
2. Julia
   - [Install](https://ferrolho.github.io/blog/2019-01-26/how-to-install-julia-on-ubuntu) Julia binaries.
3. Add Julia to Jupyter
   - [Install](https://datatofish.com/add-julia-to-jupyter/) IJulia.

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

   
