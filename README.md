### **Formal Reasoning About Port-Hamiltonian Systems in Lean4**



This repository contains a Lean 4 formalization of Hamiltonian and Port-Hamiltonian systems, with a focus on energy-based properties (energy conservation, dissipation, power balance, and passivity) and their application to robotic and mechanical systems.

The development is intended to support formal verification research in control theory and robotics, and is designed to be reproducible, modular, and theory-oriented, rather than simulation-based.



##### **Main Contributions**

This project provides:

* A unified formal framework for Hamiltonian systems and Port-Hamiltonian systems in Lean 4
*  Formal definitions of

          Hamiltonian functions and gradients

          Skew-symmetric structure matrices

          Dissipation matrices and positive semidefiniteness

*  Rigorous proofs of core system properties:

          Energy conservation (Hamiltonian systems)

          Energy dissipation (Port-Hamiltonian systems)

          Power balance identity

          Passivity

         Interconnectivity

* A formally verified embedding from Hamiltonian systems into Port-Hamiltonian systems
* A verified framework for power-conserving interconnection of Port-Hamiltonian subsystems
* Case studies:

          Single-link robotic arm

          A bio-inspired quadruped robot



##### **Project Structure**

├── Port-Hamiltonian.lean                # Main formalization file

├── lakefile.toml            # Lake project configuration

├── lake-manifest.json       # Dependency lock file

├── lean-toolchain           # Lean compiler version

├── README.md                # This file

└── .github                 # (Optional) CI configuration

The core development is contained in kuangjia.lean, organized under the namespace "PH".



##### **Formalized Theory Overview**

###### **1. Basic Mathematical Infrastructure**

* Finite-dimensional state spaces modeled as "Fin n → ℝ"
* Smooth functions and vector fields
* Gradient operator defined via "fderiv"
* Matrix properties:

          Skew-symmetry

          Symmetry

          Positive semidefiniteness

*  Block-diagonal matrices and vector projections

These components form the foundation for energy-based reasoning.

###### **2. Hamiltonian Systems**

A Hamiltonian system is defined as:

*structure HamiltonianSystem (n : Nat) where*

*H : SmoothFunction n*

*J : Matrix (Fin n) (Fin n) ℝ*

*skew : IsSkewSymmetric J*



**Proven Property**

* Energy conservation

This is formally proven using the skew-symmetry of the structure matrix.



###### **3. Port-Hamiltonian Systems**

A Port-Hamiltonian system extends Hamiltonian systems by adding dissipation and ports:

*structure PHSystem (n m : ℕ) where*

*H : SmoothFunction n*

*J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ*

*R : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ*

*G : (Fin n → ℝ) → Matrix (Fin n) (Fin m) ℝ*

*...*

with the dynamic equations and output equations.



###### **4. Verified System Properties**

For Port-Hamiltonian systems, the following properties are formally proven:

* Energy conservation (when "R = 0" and "u = 0")
* Energy dissipation (when "R" is positive semidefinite)
* Power balance identity
* Passivity
* Interconnectivity



###### **5. Embedding: Hamiltonian → Port-Hamiltonian**

A Hamiltonian system is embedded into a Port-Hamiltonian system with:

* Zero dissipation (R = 0)
* No external ports (m = 0)

The embedding is proven to preserve:

* Dynamics
* Energy rate
* Energy conservation



##### **Applications**

###### **Single-Link Robotic Arm**

* Modeled as a Port-Hamiltonian system
* Formal verification of:

          Energy conservation (d = 0)

          Energy dissipation (d ≥ 0)

          Power balance

          Passivity

###### **A bio-inspired quadruped robot**

* Each mass modeled as a PH subsystem
* Interconnected via structural coupling
* Formal proof that the interconnected system(Preserves PH structure)



##### **How to Build**

###### **Requirements**

* Lean 4 (version specified in "lean-toolchain")
* Lake

###### **Build**

*lake build*

All theorems in "kuangjia.lean" should type-check successfully.



##### **Notes**

* The development is theory-driven and does not rely on numerical simulation.
* All results are proven within Lean 4 using Mathlib.
* The code is structured to support future extensions to more complex robotic systems.
