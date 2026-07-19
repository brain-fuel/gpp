" G++ syntax: Go plus gpp constructs. Tree-sitter users get richer
" highlighting from tree-sitter-gpp; this file is the portable fallback.
if exists("b:current_syntax")
  finish
endif
runtime! syntax/go.vim
unlet! b:current_syntax
syn keyword gppKeyword enum match class instance law total delegate nat mult refl
syn match gppPipe "|>"
syn match gppKleisli ">=>"
syn match gppDirective "//gpp:\w\+.*$"
syn match gppQuantity "\v%((\(|,)\s*)@<=[01]\s+\ze\w"
hi def link gppKeyword Keyword
hi def link gppPipe Operator
hi def link gppKleisli Operator
hi def link gppDirective SpecialComment
hi def link gppQuantity StorageClass
let b:current_syntax = "gpp"
