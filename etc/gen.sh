#!/bin/sh -e

STRINGEXT=`ocamlfind query stringext`
DEPS="-I ${STRINGEXT} stringext.cma"
ocaml ${DEPS} etc/gen_services.ml etc/services.short > lib/uri_services.ml
cat etc/uri_services_raw.ml >> lib/uri_services.ml
ocaml ${DEPS} etc/gen_services.ml etc/services.full > lib/uri_services_full.ml
cat etc/uri_services_raw.ml >> lib/uri_services_full.ml
