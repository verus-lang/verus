# Installing and configuring Singular

Singular must be installed in order to use the [`integer_ring` solver mode](./nonlinear.md#2-proving-ring-based-properties-integer_ring).

**Steps:**

1. Install Singular
    - To use Singular's standard library, you need more than just the Singular executable binary. 
      Hence, when possible, we strongly recommend using your system's package manager.  Regardless of the method you select, please install Singular version 4.3.2: other versions are untested, and 4.4.0 is known to be incompatible with Verus.  Here are 
      some suggested steps for different platforms.
        - Mac: `brew install Singular` and set the `VERUS_SINGULAR_PATH` environment variable when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/local/bin/Singular`). For more options, see Singular's [OS X installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-os-x.html). 

        - Debian-based Linux: `apt-get install singular` and set the `VERUS_SINGULAR_PATH` environment variable when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/bin/Singular`). For more options, see Singular's [Linux installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-linuxunix.html).

        - Windows: See Singular's [Windows installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-windows.html).

2. Compiling Verus with Singular Support
    - The `integer_ring` functionality is conditionally compiled when the `singular` feature is set.
      To add this feature, add the `--features singular` flag when you invoke `vargo build` to compile Verus.
