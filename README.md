# Mechanisation of probabilistic designs in Isabelle/UTP
This repository contains our mechanisation of the theory of probabilistic designs (see papers: [Deriving Probabilistic Semantics Via the ‘Weakest Completion’](https://link.springer.com/chapter/10.1007/978-3-540-30482-1_17) and [Probabilistic Semantics for RoboChart: A Weakest Completion Approach](https://link.springer.com/chapter/11.1007/978-3-030-31038-7_5)) in [Isabelle/UTP](https://github.com/isabelle-utp/utp-main), a UTP proof framework in Isabelle/HOL.

This mechanisation relies on a version of Isabelle/UTP that is based on [Isabelle2019](https://isabelle.in.tum.de/website-Isabelle2019/index.html). This version of Isabelle/UTP is included in our release tag ["ramics2021r"](https://github.com/RandallYe/probabilistic_designs/releases/tag/ramics2021r).

# Installation/Set up instructions
This instruction is based on Ubuntu/Linux. It would be similar on other operation systems.

1. Download **Isabelle2019_linux.tar.gz** from [here](https://isabelle.in.tum.de/website-Isabelle2019/index.html).
2. Uncompress it inside a folder, such as "/path/to/ramics2021_prob":
  > `/path/to/ramics2021_prob $ tar zxvf Isabelle2019_linux.tar.gz`
3. Download the Isabelle/UTP version (**utp-main.ramics2021.tar.gz**) for Isabelle2019 from [here](https://github.com/RandallYe/probabilistic_designs/releases/download/ramics2021r/utp-main.ramics2021.tar.gz)
4. Uncompress it to the same folder
  > `/path/to/ramics2021_prob $ tar zxvf utp-main.ramics2021.tar.gz`
5. Clone this repository inside the same folder
  > `/path/to/ramics2021_prob $ git clone https://github.com/RandallYe/probabilistic_designs.git`
6. Add this folder to the **ROOTS** file of the Isabelle2019 installation
  > `/path/to/ramics2021_prob $ echo "/path/to/ramics2021_prob" >> Isabelle2019/ROOTS`
7. Add a **ROOT** file in the folder with the following contents
  > `/path/to/ramics2021_prob $ echo "utp-main.ramics2021/" > ROOTS`
    `/path/to/ramics2021_prob $ echo "probabilistic_designs/" >> ROOTS`
8. Build the **UTP-Prob-Designs** session [optional], then you don't need to build the seesion every time when you launch the session on Isabelle. Also, the document (**document.pdf**) in this repository will be generated in the folder _output_ under "probabilistic_designs/probability"
  > `/path/to/ramics2021_prob $ ./Isabelle2019/bin/isabelle build -b UTP-Prob-Designs`
9. Launch Isabelle2019
  > `/path/to/ramics2021_prob $ ./Isabelle2019/bin/isabelle jedit -l UTP-Hybrid-Imports`
10. Open the theory files of this repository, such as "probabilistic_designs/probability/utp_prob_HKM_ex33.thy", and wait for a while and you will see the theory is loaded and the theorems are proved.
