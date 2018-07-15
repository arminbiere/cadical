Scripts needed for the build process

  make-config-header.sh  # generates 'config.hpp'
  get-git-id.sh          # get GIT id (needed by 'make-config-headers.sh')

then scripts for producing a source release

  make-src-release.sh              # tar ball 'cadical-VERSION-GITID.tar.xz'
  prepare-sc2018-submission.sh     # star-exec format for the SAT competition

and scripts for testing and debugging

  generate-embedded-options-default-list.sh  # in 'c --opt=val' format
  generate-options-range-list.sh             # 'cnfuzz' option file format
  run-cadical-and-check-proof.sh             # wrapper to check proofs too

and finally a script to normalize white space of the source code

  normalize-white-space.sh
