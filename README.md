# HILECOP verification project (VerHilecop)

The HILECOP verification project (VerHilecop) aims at the formal
verification of HILECOP, a methodology for the design and
production/synthesis of safety-critical digital systems.

In HILECOP, high-level models based on a particular kind of Petri nets
(called SITPNs for Synchronously executed Interpreted Time Petri Nets)
represent the architecture and the behavior of digital systems. Then,
through a model-to-text transformation, VHDL code is generated from
the models, and finally the code is compiled and synthetized into a
logical circuit implemented on FPGA (Field-Programmable Gate Array
circuit) or an ASIC (Application-Specific Intergrated Circuit).

The project VerHilecop purpose is to ensure that, through the
model-to-text transformation, the behavior of digital systems
described with PN-based models is preserved in VHDL code. The goal of
the verification is to prove a behavior preservation theorem for the
HILECOP model-to-text transformation, and, to mechanize the proof with
the Coq proof assistant.

## Project architecture

- **common** : Contains types, functions, lemmas and tactics used
  	       throughout the whole project. 

- **sitpn** : Contains the declaration of the SITPN structure, the
              implementation of the SITPN semantics.
	      
- **hvhdl** : Contains the definition of H-VHDL (i.e, a subset of
  	      VHDL) syntax and semantics. Also contains the full
  	      definition of the Place and Transition designs in H-VHDL
  	      abstract syntax.

- **transformation** : Contains the implementation of HILECOP
    		       model-to-text transformation, along with lemmas
    		       about the transformation.

- **behavior-preservation** : Contains the declaration and the proof
  			      of the theorem of behavior preservation.

- **test** : Contains examples of SITPN models in the `sitpn`
  	     subfolder (PDF and Coq structure). Contains examples of
  	     H-VHDL designs in the `hvhdl` subfolder.

## Building the project

### Pre-requisites

You must install Coq v.8.9 (or >) before trying to build the project.
You also need `make`. 
All following commands must be executed in the directory containing 
this README file.

### Building procedure

- Type `make without-proof` if you want to compile only the files
  related to the specification of the SITPN and the H-VHDL semantics,
  and the files related to the transformation.

- Type `make with-proof` if you want to compile all files, including
  the files related to the proof of the behavior preservation theorem
  (i.e. the files under the `proofs/` subfolders and the `soundness`
  folder).

- Type `make cleanall` if you want to delete the files generated by a
  previous build procedure.
	      
## License

This software is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software.  You can use,
modify and/ or redistribute the software under the terms of the
CeCILL-C license as circulated by CEA, CNRS and INRIA at the following
URL "http://www.cecill.info".
