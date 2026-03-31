leanblueprint-light pdf
leanblueprint-light web
LEAN_NUM_THREADS=1 lake build
lake exe mk_all
lake exe checkdecls blueprint/lean_decls
