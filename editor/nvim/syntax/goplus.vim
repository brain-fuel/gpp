" Go+ syntax: Go plus goplus constructs. Tree-sitter users get richer
" highlighting from tree-sitter-goplus; this file is the portable fallback.
if exists("b:current_syntax")
  finish
endif
runtime! syntax/go.vim
unlet! b:current_syntax
syn keyword goplusKeyword enum match class instance law total delegate nat mult refl
syn match goplusPipe "|>"
syn match goplusKleisli ">=>"
syn match goplusDirective "//goplus:\w\+.*$"
syn match goplusQuantity "\v%((\(|,)\s*)@<=[01]\s+\ze\w"
hi def link goplusKeyword Keyword
hi def link goplusPipe Operator
hi def link goplusKleisli Operator
hi def link goplusDirective SpecialComment
hi def link goplusQuantity StorageClass
let b:current_syntax = "goplus"
