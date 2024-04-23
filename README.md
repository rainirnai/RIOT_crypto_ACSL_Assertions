# RIOT_crypto_ACSL_Assertions
The RIOT IoT OS crypto library with ACSL assertions for verification with Frama-C for run-time errors
The RIOT IoT OS crypto library files present here contains ACSL assertions to check the runtime errors for RIOT OS using the Frama-C tool.

We used Ubuntu version 22.04 in Oracle VirtualBox Version 7.0 to run the Frama-C software. The Frama-C software version was 25.0 (Manganese). 

Please follow the steps below in order to replicate the tests in your device.

* Open the terminal in the Ubuntu OS in VirtualBox or your own device.
* Note some commands may require sudo.
* Install opam first which is the OCaml package manager.
  ``` sudo apt install opam
  ```
* Initialize opam (install OCaml compiler)
  ``` opam init --compiler 4.14.1
      eval $(opam env)
  ```
* Install Frama-C (including dependencies)
  ``` opam install frama-c 
  ```
