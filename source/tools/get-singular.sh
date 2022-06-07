#! /bin/bash

# Note: to use standard libary(which includes Groebner basis), it is not desired to just grap Singular executable binary 

# Mac:
# OS X installation guide: https://www.singular.uni-kl.de/index.php/singular-download/install-os-x.html
# downloadable mac binary not available: brew install OR download dmg file from the above url
#     brew install Singular
#     Add VERUS_SINGULAR_PATH when running Verus. (e.g. VERUS_SINGULAR_PATH=/usr/local/bin/Singular)


# Linux:
# Linux installation guide: https://www.singular.uni-kl.de/index.php/singular-download/install-linuxunix.html      
if [ `uname` == "Linux" ]; then
    wget https://service.mathematik.uni-kl.de/ftp/pub/Math/Singular/UNIX/Singular-4.2.1-x86_64-Linux.tar.gz
    mkdir Singular-4.2.1-x86_64-Linux
    tar -xf Singular-4.2.1-x86_64-Linux.tar.gz  --directory ./Singular-4.2.1-x86_64-Linux
    cp Singular-4.2.1-x86_64-Linux/bin/Singular .
    rm Singular-4.2.1-x86_64-Linux.tar.gz

    ## alternatively, you can do below
    # apt-get update
    # apt-get install singular
    ## Add VERUS_SINGULAR_PATH when running Verus. (e.g. VERUS_SINGULAR_PATH=/usr/bin/Singular)

fi


# Windows:
# Windows installation guide: https://www.singular.uni-kl.de/index.php/singular-download/install-windows.html