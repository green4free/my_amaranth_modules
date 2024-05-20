# my_amaranth_modules
## A collection of basic building block modules in amaranth that are usefull in multiple of my projects.

Some parts rely on code from amlib https://github.com/amaranth-farm/amlib
and some use features that I have added in the amaranth branch https://github.com/green4free/amaranth/tree/ugly_hacks_to_avoid_creating_duplicate_modules
more precisely the function setPureIdentifier that collect the paramters used when instanciating a module, and lets the programmer promise that module elaboration is pure, so that code doesn't have to be re-generated for that module if it is created again with the same parameters. But it is still a bit ugly done, so I have not tried to get it upstreamed.