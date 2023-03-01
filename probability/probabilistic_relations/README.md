# Mechanisation of probabilistic designs in Isabelle/UTP
This folder (`probabilistic_relations`) contains our mechanisation of the theory of probabilistic relations in [Isabelle/UTP](https://isabelle-utp.york.ac.uk/), a UTP proof framework in Isabelle/HOL.

# Installation/Set up instructions
This instruction is based on Ubuntu/Linux. It would be similar on other operation systems.

## Clone this repository
1. Clone and enter the folder of this probabilistic relations
```
/path/to/yourfolder $ git clone https://github.com/RandallYe/probabilistic_programming_utp.git
/path/to/yourfolder $ cd probabilistic_programming_utp/probability/probabilistic_relations/
```
We use `/path/to/.../probabilistic_relations/` to denote the path to this particular directory.
2. Switch to the branch `TCS` in this case
```
/path/to/.../probabilistic_relations/ (main) $ git checkout TCS
/path/to/.../probabilistic_relations/ (TCS) $ 
```

## Isabelle/UTP distributions with prebuild heap images on Linux

1. Download Isabelle/UTP distributions from [here](https://isabelle-utp.york.ac.uk/download) and choose `Isabelle2021-1 on Linux (January 26th 2023)`, it is `Isabelle2021-1-CyPhyAssure-20230126.tar.bz2` in this case
2. Uncompress it inside a folder, such as "/path/to/yourfolder":
```
/path/to/yourfolder $ tar -xvjf Isabelle2021-1-CyPhyAssure-20230126.tar.bz2
/path/to/yourfolder $ cd Isabelle2021-1-CyPhyAssure/
```
3. Depending on your purposes of using this repository, choose one way to Launch Isabelle/UTP
- for the development of probabilistic relations theories, go to Step 4.
- for the development of examples using probabilistic relations theories, go to Step 5.
4. Launch Isabelle/UTP with session `UTP2`
```
/path/to/yourfolder/Isabelle2021-1-CyPhyAssure/ $ ./bin/isabelle jedit -l UTP2
```
When it is the first time to load this, it takes a bit time to finish building of the session `UTP2`. Then you can load the probabilistic relations theories: open `utp_prob_rel.thy` under `/path/to/.../probabilistic_relations/` in Isabelle/jedit. 

5. Launch Isabelle/UTP with session `UTP_prob_relations`
```
/path/to/yourfolder/Isabelle2021-1-CyPhyAssure/ $ bin/isabelle jedit -d ../probabilistic_programming_utp/probability/probabilistic_relations/ -l UTP_prob_relations
```
When it is the first time to load this, it takes a bit time to finish building of the session `UTP_prob_relations`. Then load one of the probabilistic relations examples: open `utp_prob_rel_lattice_coin.thy` under `/path/to/.../probabilistic_relations/Examples` in Isabelle/jedit. 

## Standard
1. Download **Isabelle2021-1_linux.tar.gz** from [here](https://isabelle.in.tum.de/website-Isabelle2021-1/index.html).
2. Uncompress it inside a folder, such as "/path/to/yourfolder":
```
/path/to/yourfolder $ tar zxvf Isabelle2021-1_linux.tar.gz
``` 
3. Clone CyPhyAssure meta-repository (which is updated periodically to sync and try to keep in a stable state) from [here](https://github.com/isabelle-utp/CyPhyAssure) and checkout all submodules
```
/path/to/yourfolder $ git clone https://github.com/isabelle-utp/CyPhyAssure.git
/path/to/yourfolder $ cd CyPhyAssure
/path/to/yourfolder/CyPhyAssure (main) $ git submodule update --init --recursive
```
4. Depending on your purposes of using this repository, choose one way to Launch Isabelle/UTP
- for the development of probabilistic relations theories, go to Step 5.
- for the development of examples using probabilistic relations theories, go to Step 6.
5. Launch Isabelle/UTP with session `UTP2`
```
/path/to/yourfolder $ ./Isabelle2021-1/bin/isabelle jedit -d CyPhyAssure -l UTP2
```
When it is the first time to load this, it takes a bit long time to finish building of the session `UTP2`. Then you can load the probabilistic relations theories: open `utp_prob_rel.thy` under `/path/to/.../probabilistic_relations/` in Isabelle/jedit. 

6. Launch Isabelle/UTP with session `UTP_prob_relations`
```
/path/to/yourfolder/Isabelle2021-1-CyPhyAssure/ $ ./Isabelle2021-1/bin/isabelle jedit -d CyPhyAssure -d ./probabilistic_programming_utp/probability/probabilistic_relations/ -l UTP_prob_relations
```
When it is the first time to load this, it takes a bit long time to finish building of the session `UTP_prob_relations`. Then load one of the probabilistic relations examples: open `utp_prob_rel_lattice_coin.thy` under `/path/to/.../probabilistic_relations/Examples` in Isabelle/jedit. 