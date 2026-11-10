import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace Out

inductive large_variant_chunk0 (k_a : Type) where
  | C0 (_ : k_a)
  | C1 (_ : k_a)
  | C2 (_ : k_a)
  | C3 (_ : k_a)
  | C4 (_ : k_a)
  | C5 (_ : k_a)
  | C6 (_ : k_a)
  | C7 (_ : k_a)
  | C8 (_ : k_a)
  | C9 (_ : k_a)
  | C10 (_ : k_a)
  | C11 (_ : k_a)
  | C12 (_ : k_a)
  | C13 (_ : k_a)
  | C14 (_ : k_a)
  | C15 (_ : k_a)
  | C16 (_ : k_a)
  | C17 (_ : k_a)
  | C18 (_ : k_a)
  | C19 (_ : k_a)
  | C20 (_ : k_a)
  | C21 (_ : k_a)
  | C22 (_ : k_a)
  | C23 (_ : k_a)
  | C24 (_ : k_a)
  | C25 (_ : k_a)
  | C26 (_ : k_a)
  | C27 (_ : k_a)
  | C28 (_ : k_a)
  | C29 (_ : k_a)
  | C30 (_ : k_a)
  | C31 (_ : k_a)
  | C32 (_ : k_a)
  | C33 (_ : k_a)
  | C34 (_ : k_a)
  | C35 (_ : k_a)
  | C36 (_ : k_a)
  | C37 (_ : k_a)
  | C38 (_ : k_a)
  | C39 (_ : k_a)
  | C40 (_ : k_a)
  | C41 (_ : k_a)
  | C42 (_ : k_a)
  | C43 (_ : k_a)
  | C44 (_ : k_a)
  | C45 (_ : k_a)
  | C46 (_ : k_a)
  | C47 (_ : k_a)
  | C48 (_ : k_a)
  | C49 (_ : k_a)
  | C50 (_ : k_a)
  | C51 (_ : k_a)
  | C52 (_ : k_a)
  | C53 (_ : k_a)
  | C54 (_ : k_a)
  | C55 (_ : k_a)
  | C56 (_ : k_a)
  | C57 (_ : k_a)
  | C58 (_ : k_a)
  | C59 (_ : k_a)
  | C60 (_ : k_a)
  | C61 (_ : k_a)
  | C62 (_ : k_a)
  | C63 (_ : k_a)
  | C64 (_ : k_a)
  | C65 (_ : k_a)
  | C66 (_ : k_a)
  | C67 (_ : k_a)
  | C68 (_ : k_a)
  | C69 (_ : k_a)
  | C70 (_ : k_a)
  | C71 (_ : k_a)
  | C72 (_ : k_a)
  | C73 (_ : k_a)
  | C74 (_ : k_a)
  | C75 (_ : k_a)
  | C76 (_ : k_a)
  | C77 (_ : k_a)
  | C78 (_ : k_a)
  | C79 (_ : k_a)
  | C80 (_ : k_a)
  | C81 (_ : k_a)
  | C82 (_ : k_a)
  | C83 (_ : k_a)
  | C84 (_ : k_a)
  | C85 (_ : k_a)
  | C86 (_ : k_a)
  | C87 (_ : k_a)
  | C88 (_ : k_a)
  | C89 (_ : k_a)
  | C90 (_ : k_a)
  | C91 (_ : k_a)
  | C92 (_ : k_a)
  | C93 (_ : k_a)
  | C94 (_ : k_a)
  | C95 (_ : k_a)
  | C96 (_ : k_a)
  | C97 (_ : k_a)
  | C98 (_ : k_a)
  | C99 (_ : k_a)
  | C100 (_ : k_a)
  | C101 (_ : k_a)
  | C102 (_ : k_a)
  | C103 (_ : k_a)
  | C104 (_ : k_a)
  | C105 (_ : k_a)
  | C106 (_ : k_a)
  | C107 (_ : k_a)
  | C108 (_ : k_a)
  | C109 (_ : k_a)
  | C110 (_ : k_a)
  | C111 (_ : k_a)
  | C112 (_ : k_a)
  | C113 (_ : k_a)
  | C114 (_ : k_a)
  | C115 (_ : k_a)
  | C116 (_ : k_a)
  | C117 (_ : k_a)
  | C118 (_ : k_a)
  | C119 (_ : k_a)
  | C120 (_ : k_a)
  | C121 (_ : k_a)
  | C122 (_ : k_a)
  | C123 (_ : k_a)
  | C124 (_ : k_a)
  | C125 (_ : k_a)
  | C126 (_ : k_a)
  | C127 (_ : k_a)
  | C128 (_ : k_a)
  | C129 (_ : k_a)
  | C130 (_ : k_a)
  | C131 (_ : k_a)
  | C132 (_ : k_a)
  | C133 (_ : k_a)
  | C134 (_ : k_a)
  | C135 (_ : k_a)
  | C136 (_ : k_a)
  | C137 (_ : k_a)
  | C138 (_ : k_a)
  | C139 (_ : k_a)
  | C140 (_ : k_a)
  | C141 (_ : k_a)
  | C142 (_ : k_a)
  | C143 (_ : k_a)
  | C144 (_ : k_a)
  | C145 (_ : k_a)
  | C146 (_ : k_a)
  | C147 (_ : k_a)
  | C148 (_ : k_a)
  | C149 (_ : k_a)
  | C150 (_ : k_a)
  | C151 (_ : k_a)
  | C152 (_ : k_a)
  | C153 (_ : k_a)
  | C154 (_ : k_a)
  | C155 (_ : k_a)
  | C156 (_ : k_a)
  | C157 (_ : k_a)
  | C158 (_ : k_a)
  | C159 (_ : k_a)
  | C160 (_ : k_a)
  | C161 (_ : k_a)
  | C162 (_ : k_a)
  | C163 (_ : k_a)
  | C164 (_ : k_a)
  | C165 (_ : k_a)
  | C166 (_ : k_a)
  | C167 (_ : k_a)
  | C168 (_ : k_a)
  | C169 (_ : k_a)
  | C170 (_ : k_a)
  | C171 (_ : k_a)
  | C172 (_ : k_a)
  | C173 (_ : k_a)
  | C174 (_ : k_a)
  | C175 (_ : k_a)
  | C176 (_ : k_a)
  | C177 (_ : k_a)
  | C178 (_ : k_a)
  | C179 (_ : k_a)
  | C180 (_ : k_a)
  | C181 (_ : k_a)
  | C182 (_ : k_a)
  | C183 (_ : k_a)
  | C184 (_ : k_a)
  | C185 (_ : k_a)
  | C186 (_ : k_a)
  | C187 (_ : k_a)
  | C188 (_ : k_a)
  | C189 (_ : k_a)
  | C190 (_ : k_a)
  | C191 (_ : k_a)
  | C192 (_ : k_a)
  | C193 (_ : k_a)
  | C194 (_ : k_a)
  | C195 (_ : k_a)
  | C196 (_ : k_a)
  | C197 (_ : k_a)
  | C198 (_ : k_a)
  | C199 (_ : k_a)
  | C200 (_ : k_a)
  | C201 (_ : k_a)
  | C202 (_ : k_a)
  | C203 (_ : k_a)
  | C204 (_ : k_a)
  | C205 (_ : k_a)
  | C206 (_ : k_a)
  | C207 (_ : k_a)
  | C208 (_ : k_a)
  | C209 (_ : k_a)
  | C210 (_ : k_a)
  | C211 (_ : k_a)
  | C212 (_ : k_a)
  | C213 (_ : k_a)
  | C214 (_ : k_a)
  | C215 (_ : k_a)
  | C216 (_ : k_a)
  | C217 (_ : k_a)
  | C218 (_ : k_a)
  | C219 (_ : k_a)
  | C220 (_ : k_a)
  | C221 (_ : k_a)
  | C222 (_ : k_a)
  | C223 (_ : k_a)
  | C224 (_ : k_a)
  | C225 (_ : k_a)
  | C226 (_ : k_a)
  | C227 (_ : k_a)
  | C228 (_ : k_a)
  | C229 (_ : k_a)
  | C230 (_ : k_a)
  | C231 (_ : k_a)
  | C232 (_ : k_a)
  | C233 (_ : k_a)
  | C234 (_ : k_a)
  | C235 (_ : k_a)
  | C236 (_ : k_a)
  | C237 (_ : k_a)
  | C238 (_ : k_a)
  | C239 (_ : k_a)
  | C240 (_ : k_a)
  | C241 (_ : k_a)
  | C242 (_ : k_a)
  | C243 (_ : k_a)
  deriving Inhabited, BEq, Repr
inductive large_variant_chunk1 (k_a : Type) where
  | C244 (_ : k_a)
  deriving Inhabited, BEq, Repr
/-- Type quantifiers: k_a : Type -/
inductive large_variant (k_a : Type) where
  | chunk0 (_ : (large_variant_chunk0 k_a))
  | chunk1 (_ : (large_variant_chunk1 k_a))
  deriving Inhabited, BEq, Repr
@[match_pattern] abbrev large_variant.C0 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C0 x)
@[match_pattern] abbrev large_variant.C1 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C1 x)
@[match_pattern] abbrev large_variant.C2 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C2 x)
@[match_pattern] abbrev large_variant.C3 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C3 x)
@[match_pattern] abbrev large_variant.C4 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C4 x)
@[match_pattern] abbrev large_variant.C5 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C5 x)
@[match_pattern] abbrev large_variant.C6 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C6 x)
@[match_pattern] abbrev large_variant.C7 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C7 x)
@[match_pattern] abbrev large_variant.C8 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C8 x)
@[match_pattern] abbrev large_variant.C9 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C9 x)
@[match_pattern] abbrev large_variant.C10 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C10 x)
@[match_pattern] abbrev large_variant.C11 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C11 x)
@[match_pattern] abbrev large_variant.C12 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C12 x)
@[match_pattern] abbrev large_variant.C13 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C13 x)
@[match_pattern] abbrev large_variant.C14 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C14 x)
@[match_pattern] abbrev large_variant.C15 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C15 x)
@[match_pattern] abbrev large_variant.C16 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C16 x)
@[match_pattern] abbrev large_variant.C17 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C17 x)
@[match_pattern] abbrev large_variant.C18 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C18 x)
@[match_pattern] abbrev large_variant.C19 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C19 x)
@[match_pattern] abbrev large_variant.C20 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C20 x)
@[match_pattern] abbrev large_variant.C21 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C21 x)
@[match_pattern] abbrev large_variant.C22 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C22 x)
@[match_pattern] abbrev large_variant.C23 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C23 x)
@[match_pattern] abbrev large_variant.C24 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C24 x)
@[match_pattern] abbrev large_variant.C25 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C25 x)
@[match_pattern] abbrev large_variant.C26 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C26 x)
@[match_pattern] abbrev large_variant.C27 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C27 x)
@[match_pattern] abbrev large_variant.C28 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C28 x)
@[match_pattern] abbrev large_variant.C29 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C29 x)
@[match_pattern] abbrev large_variant.C30 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C30 x)
@[match_pattern] abbrev large_variant.C31 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C31 x)
@[match_pattern] abbrev large_variant.C32 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C32 x)
@[match_pattern] abbrev large_variant.C33 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C33 x)
@[match_pattern] abbrev large_variant.C34 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C34 x)
@[match_pattern] abbrev large_variant.C35 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C35 x)
@[match_pattern] abbrev large_variant.C36 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C36 x)
@[match_pattern] abbrev large_variant.C37 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C37 x)
@[match_pattern] abbrev large_variant.C38 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C38 x)
@[match_pattern] abbrev large_variant.C39 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C39 x)
@[match_pattern] abbrev large_variant.C40 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C40 x)
@[match_pattern] abbrev large_variant.C41 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C41 x)
@[match_pattern] abbrev large_variant.C42 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C42 x)
@[match_pattern] abbrev large_variant.C43 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C43 x)
@[match_pattern] abbrev large_variant.C44 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C44 x)
@[match_pattern] abbrev large_variant.C45 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C45 x)
@[match_pattern] abbrev large_variant.C46 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C46 x)
@[match_pattern] abbrev large_variant.C47 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C47 x)
@[match_pattern] abbrev large_variant.C48 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C48 x)
@[match_pattern] abbrev large_variant.C49 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C49 x)
@[match_pattern] abbrev large_variant.C50 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C50 x)
@[match_pattern] abbrev large_variant.C51 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C51 x)
@[match_pattern] abbrev large_variant.C52 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C52 x)
@[match_pattern] abbrev large_variant.C53 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C53 x)
@[match_pattern] abbrev large_variant.C54 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C54 x)
@[match_pattern] abbrev large_variant.C55 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C55 x)
@[match_pattern] abbrev large_variant.C56 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C56 x)
@[match_pattern] abbrev large_variant.C57 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C57 x)
@[match_pattern] abbrev large_variant.C58 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C58 x)
@[match_pattern] abbrev large_variant.C59 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C59 x)
@[match_pattern] abbrev large_variant.C60 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C60 x)
@[match_pattern] abbrev large_variant.C61 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C61 x)
@[match_pattern] abbrev large_variant.C62 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C62 x)
@[match_pattern] abbrev large_variant.C63 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C63 x)
@[match_pattern] abbrev large_variant.C64 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C64 x)
@[match_pattern] abbrev large_variant.C65 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C65 x)
@[match_pattern] abbrev large_variant.C66 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C66 x)
@[match_pattern] abbrev large_variant.C67 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C67 x)
@[match_pattern] abbrev large_variant.C68 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C68 x)
@[match_pattern] abbrev large_variant.C69 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C69 x)
@[match_pattern] abbrev large_variant.C70 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C70 x)
@[match_pattern] abbrev large_variant.C71 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C71 x)
@[match_pattern] abbrev large_variant.C72 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C72 x)
@[match_pattern] abbrev large_variant.C73 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C73 x)
@[match_pattern] abbrev large_variant.C74 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C74 x)
@[match_pattern] abbrev large_variant.C75 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C75 x)
@[match_pattern] abbrev large_variant.C76 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C76 x)
@[match_pattern] abbrev large_variant.C77 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C77 x)
@[match_pattern] abbrev large_variant.C78 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C78 x)
@[match_pattern] abbrev large_variant.C79 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C79 x)
@[match_pattern] abbrev large_variant.C80 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C80 x)
@[match_pattern] abbrev large_variant.C81 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C81 x)
@[match_pattern] abbrev large_variant.C82 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C82 x)
@[match_pattern] abbrev large_variant.C83 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C83 x)
@[match_pattern] abbrev large_variant.C84 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C84 x)
@[match_pattern] abbrev large_variant.C85 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C85 x)
@[match_pattern] abbrev large_variant.C86 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C86 x)
@[match_pattern] abbrev large_variant.C87 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C87 x)
@[match_pattern] abbrev large_variant.C88 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C88 x)
@[match_pattern] abbrev large_variant.C89 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C89 x)
@[match_pattern] abbrev large_variant.C90 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C90 x)
@[match_pattern] abbrev large_variant.C91 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C91 x)
@[match_pattern] abbrev large_variant.C92 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C92 x)
@[match_pattern] abbrev large_variant.C93 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C93 x)
@[match_pattern] abbrev large_variant.C94 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C94 x)
@[match_pattern] abbrev large_variant.C95 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C95 x)
@[match_pattern] abbrev large_variant.C96 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C96 x)
@[match_pattern] abbrev large_variant.C97 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C97 x)
@[match_pattern] abbrev large_variant.C98 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C98 x)
@[match_pattern] abbrev large_variant.C99 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C99 x)
@[match_pattern] abbrev large_variant.C100 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C100 x)
@[match_pattern] abbrev large_variant.C101 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C101 x)
@[match_pattern] abbrev large_variant.C102 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C102 x)
@[match_pattern] abbrev large_variant.C103 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C103 x)
@[match_pattern] abbrev large_variant.C104 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C104 x)
@[match_pattern] abbrev large_variant.C105 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C105 x)
@[match_pattern] abbrev large_variant.C106 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C106 x)
@[match_pattern] abbrev large_variant.C107 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C107 x)
@[match_pattern] abbrev large_variant.C108 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C108 x)
@[match_pattern] abbrev large_variant.C109 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C109 x)
@[match_pattern] abbrev large_variant.C110 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C110 x)
@[match_pattern] abbrev large_variant.C111 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C111 x)
@[match_pattern] abbrev large_variant.C112 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C112 x)
@[match_pattern] abbrev large_variant.C113 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C113 x)
@[match_pattern] abbrev large_variant.C114 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C114 x)
@[match_pattern] abbrev large_variant.C115 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C115 x)
@[match_pattern] abbrev large_variant.C116 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C116 x)
@[match_pattern] abbrev large_variant.C117 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C117 x)
@[match_pattern] abbrev large_variant.C118 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C118 x)
@[match_pattern] abbrev large_variant.C119 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C119 x)
@[match_pattern] abbrev large_variant.C120 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C120 x)
@[match_pattern] abbrev large_variant.C121 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C121 x)
@[match_pattern] abbrev large_variant.C122 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C122 x)
@[match_pattern] abbrev large_variant.C123 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C123 x)
@[match_pattern] abbrev large_variant.C124 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C124 x)
@[match_pattern] abbrev large_variant.C125 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C125 x)
@[match_pattern] abbrev large_variant.C126 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C126 x)
@[match_pattern] abbrev large_variant.C127 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C127 x)
@[match_pattern] abbrev large_variant.C128 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C128 x)
@[match_pattern] abbrev large_variant.C129 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C129 x)
@[match_pattern] abbrev large_variant.C130 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C130 x)
@[match_pattern] abbrev large_variant.C131 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C131 x)
@[match_pattern] abbrev large_variant.C132 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C132 x)
@[match_pattern] abbrev large_variant.C133 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C133 x)
@[match_pattern] abbrev large_variant.C134 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C134 x)
@[match_pattern] abbrev large_variant.C135 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C135 x)
@[match_pattern] abbrev large_variant.C136 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C136 x)
@[match_pattern] abbrev large_variant.C137 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C137 x)
@[match_pattern] abbrev large_variant.C138 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C138 x)
@[match_pattern] abbrev large_variant.C139 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C139 x)
@[match_pattern] abbrev large_variant.C140 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C140 x)
@[match_pattern] abbrev large_variant.C141 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C141 x)
@[match_pattern] abbrev large_variant.C142 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C142 x)
@[match_pattern] abbrev large_variant.C143 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C143 x)
@[match_pattern] abbrev large_variant.C144 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C144 x)
@[match_pattern] abbrev large_variant.C145 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C145 x)
@[match_pattern] abbrev large_variant.C146 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C146 x)
@[match_pattern] abbrev large_variant.C147 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C147 x)
@[match_pattern] abbrev large_variant.C148 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C148 x)
@[match_pattern] abbrev large_variant.C149 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C149 x)
@[match_pattern] abbrev large_variant.C150 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C150 x)
@[match_pattern] abbrev large_variant.C151 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C151 x)
@[match_pattern] abbrev large_variant.C152 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C152 x)
@[match_pattern] abbrev large_variant.C153 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C153 x)
@[match_pattern] abbrev large_variant.C154 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C154 x)
@[match_pattern] abbrev large_variant.C155 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C155 x)
@[match_pattern] abbrev large_variant.C156 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C156 x)
@[match_pattern] abbrev large_variant.C157 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C157 x)
@[match_pattern] abbrev large_variant.C158 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C158 x)
@[match_pattern] abbrev large_variant.C159 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C159 x)
@[match_pattern] abbrev large_variant.C160 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C160 x)
@[match_pattern] abbrev large_variant.C161 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C161 x)
@[match_pattern] abbrev large_variant.C162 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C162 x)
@[match_pattern] abbrev large_variant.C163 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C163 x)
@[match_pattern] abbrev large_variant.C164 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C164 x)
@[match_pattern] abbrev large_variant.C165 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C165 x)
@[match_pattern] abbrev large_variant.C166 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C166 x)
@[match_pattern] abbrev large_variant.C167 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C167 x)
@[match_pattern] abbrev large_variant.C168 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C168 x)
@[match_pattern] abbrev large_variant.C169 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C169 x)
@[match_pattern] abbrev large_variant.C170 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C170 x)
@[match_pattern] abbrev large_variant.C171 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C171 x)
@[match_pattern] abbrev large_variant.C172 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C172 x)
@[match_pattern] abbrev large_variant.C173 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C173 x)
@[match_pattern] abbrev large_variant.C174 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C174 x)
@[match_pattern] abbrev large_variant.C175 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C175 x)
@[match_pattern] abbrev large_variant.C176 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C176 x)
@[match_pattern] abbrev large_variant.C177 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C177 x)
@[match_pattern] abbrev large_variant.C178 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C178 x)
@[match_pattern] abbrev large_variant.C179 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C179 x)
@[match_pattern] abbrev large_variant.C180 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C180 x)
@[match_pattern] abbrev large_variant.C181 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C181 x)
@[match_pattern] abbrev large_variant.C182 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C182 x)
@[match_pattern] abbrev large_variant.C183 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C183 x)
@[match_pattern] abbrev large_variant.C184 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C184 x)
@[match_pattern] abbrev large_variant.C185 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C185 x)
@[match_pattern] abbrev large_variant.C186 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C186 x)
@[match_pattern] abbrev large_variant.C187 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C187 x)
@[match_pattern] abbrev large_variant.C188 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C188 x)
@[match_pattern] abbrev large_variant.C189 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C189 x)
@[match_pattern] abbrev large_variant.C190 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C190 x)
@[match_pattern] abbrev large_variant.C191 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C191 x)
@[match_pattern] abbrev large_variant.C192 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C192 x)
@[match_pattern] abbrev large_variant.C193 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C193 x)
@[match_pattern] abbrev large_variant.C194 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C194 x)
@[match_pattern] abbrev large_variant.C195 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C195 x)
@[match_pattern] abbrev large_variant.C196 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C196 x)
@[match_pattern] abbrev large_variant.C197 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C197 x)
@[match_pattern] abbrev large_variant.C198 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C198 x)
@[match_pattern] abbrev large_variant.C199 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C199 x)
@[match_pattern] abbrev large_variant.C200 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C200 x)
@[match_pattern] abbrev large_variant.C201 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C201 x)
@[match_pattern] abbrev large_variant.C202 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C202 x)
@[match_pattern] abbrev large_variant.C203 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C203 x)
@[match_pattern] abbrev large_variant.C204 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C204 x)
@[match_pattern] abbrev large_variant.C205 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C205 x)
@[match_pattern] abbrev large_variant.C206 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C206 x)
@[match_pattern] abbrev large_variant.C207 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C207 x)
@[match_pattern] abbrev large_variant.C208 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C208 x)
@[match_pattern] abbrev large_variant.C209 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C209 x)
@[match_pattern] abbrev large_variant.C210 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C210 x)
@[match_pattern] abbrev large_variant.C211 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C211 x)
@[match_pattern] abbrev large_variant.C212 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C212 x)
@[match_pattern] abbrev large_variant.C213 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C213 x)
@[match_pattern] abbrev large_variant.C214 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C214 x)
@[match_pattern] abbrev large_variant.C215 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C215 x)
@[match_pattern] abbrev large_variant.C216 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C216 x)
@[match_pattern] abbrev large_variant.C217 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C217 x)
@[match_pattern] abbrev large_variant.C218 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C218 x)
@[match_pattern] abbrev large_variant.C219 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C219 x)
@[match_pattern] abbrev large_variant.C220 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C220 x)
@[match_pattern] abbrev large_variant.C221 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C221 x)
@[match_pattern] abbrev large_variant.C222 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C222 x)
@[match_pattern] abbrev large_variant.C223 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C223 x)
@[match_pattern] abbrev large_variant.C224 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C224 x)
@[match_pattern] abbrev large_variant.C225 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C225 x)
@[match_pattern] abbrev large_variant.C226 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C226 x)
@[match_pattern] abbrev large_variant.C227 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C227 x)
@[match_pattern] abbrev large_variant.C228 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C228 x)
@[match_pattern] abbrev large_variant.C229 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C229 x)
@[match_pattern] abbrev large_variant.C230 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C230 x)
@[match_pattern] abbrev large_variant.C231 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C231 x)
@[match_pattern] abbrev large_variant.C232 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C232 x)
@[match_pattern] abbrev large_variant.C233 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C233 x)
@[match_pattern] abbrev large_variant.C234 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C234 x)
@[match_pattern] abbrev large_variant.C235 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C235 x)
@[match_pattern] abbrev large_variant.C236 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C236 x)
@[match_pattern] abbrev large_variant.C237 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C237 x)
@[match_pattern] abbrev large_variant.C238 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C238 x)
@[match_pattern] abbrev large_variant.C239 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C239 x)
@[match_pattern] abbrev large_variant.C240 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C240 x)
@[match_pattern] abbrev large_variant.C241 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C241 x)
@[match_pattern] abbrev large_variant.C242 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C242 x)
@[match_pattern] abbrev large_variant.C243 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk0 (large_variant_chunk0.C243 x)
@[match_pattern] abbrev large_variant.C244 {k_a : Type} (x : k_a) : large_variant k_a := large_variant.chunk1 (large_variant_chunk1.C244 x)
open large_variant

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim



abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception




XXXXXXXXX

import Sail
import Out.Defs
import Out.SpecializationV1
import Out.FakeReal

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace Out

open ConcurrencyInterfaceV1

namespace Functions

open large_variant

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: k_a : Type -/
def tag (x : (large_variant k_a)) : Int :=
  match x with
  | .C0 _ => 0
  | .C1 _ => 1
  | .C2 _ => 2
  | .C3 _ => 3
  | .C4 _ => 4
  | .C5 _ => 5
  | .C6 _ => 6
  | .C7 _ => 7
  | .C8 _ => 8
  | .C9 _ => 9
  | .C10 _ => 10
  | .C11 _ => 11
  | .C12 _ => 12
  | .C13 _ => 13
  | .C14 _ => 14
  | .C15 _ => 15
  | .C16 _ => 16
  | .C17 _ => 17
  | .C18 _ => 18
  | .C19 _ => 19
  | .C20 _ => 20
  | .C21 _ => 21
  | .C22 _ => 22
  | .C23 _ => 23
  | .C24 _ => 24
  | .C25 _ => 25
  | .C26 _ => 26
  | .C27 _ => 27
  | .C28 _ => 28
  | .C29 _ => 29
  | .C30 _ => 30
  | .C31 _ => 31
  | .C32 _ => 32
  | .C33 _ => 33
  | .C34 _ => 34
  | .C35 _ => 35
  | .C36 _ => 36
  | .C37 _ => 37
  | .C38 _ => 38
  | .C39 _ => 39
  | .C40 _ => 40
  | .C41 _ => 41
  | .C42 _ => 42
  | .C43 _ => 43
  | .C44 _ => 44
  | .C45 _ => 45
  | .C46 _ => 46
  | .C47 _ => 47
  | .C48 _ => 48
  | .C49 _ => 49
  | .C50 _ => 50
  | .C51 _ => 51
  | .C52 _ => 52
  | .C53 _ => 53
  | .C54 _ => 54
  | .C55 _ => 55
  | .C56 _ => 56
  | .C57 _ => 57
  | .C58 _ => 58
  | .C59 _ => 59
  | .C60 _ => 60
  | .C61 _ => 61
  | .C62 _ => 62
  | .C63 _ => 63
  | .C64 _ => 64
  | .C65 _ => 65
  | .C66 _ => 66
  | .C67 _ => 67
  | .C68 _ => 68
  | .C69 _ => 69
  | .C70 _ => 70
  | .C71 _ => 71
  | .C72 _ => 72
  | .C73 _ => 73
  | .C74 _ => 74
  | .C75 _ => 75
  | .C76 _ => 76
  | .C77 _ => 77
  | .C78 _ => 78
  | .C79 _ => 79
  | .C80 _ => 80
  | .C81 _ => 81
  | .C82 _ => 82
  | .C83 _ => 83
  | .C84 _ => 84
  | .C85 _ => 85
  | .C86 _ => 86
  | .C87 _ => 87
  | .C88 _ => 88
  | .C89 _ => 89
  | .C90 _ => 90
  | .C91 _ => 91
  | .C92 _ => 92
  | .C93 _ => 93
  | .C94 _ => 94
  | .C95 _ => 95
  | .C96 _ => 96
  | .C97 _ => 97
  | .C98 _ => 98
  | .C99 _ => 99
  | .C100 _ => 100
  | .C101 _ => 101
  | .C102 _ => 102
  | .C103 _ => 103
  | .C104 _ => 104
  | .C105 _ => 105
  | .C106 _ => 106
  | .C107 _ => 107
  | .C108 _ => 108
  | .C109 _ => 109
  | .C110 _ => 110
  | .C111 _ => 111
  | .C112 _ => 112
  | .C113 _ => 113
  | .C114 _ => 114
  | .C115 _ => 115
  | .C116 _ => 116
  | .C117 _ => 117
  | .C118 _ => 118
  | .C119 _ => 119
  | .C120 _ => 120
  | .C121 _ => 121
  | .C122 _ => 122
  | .C123 _ => 123
  | .C124 _ => 124
  | .C125 _ => 125
  | .C126 _ => 126
  | .C127 _ => 127
  | .C128 _ => 128
  | .C129 _ => 129
  | .C130 _ => 130
  | .C131 _ => 131
  | .C132 _ => 132
  | .C133 _ => 133
  | .C134 _ => 134
  | .C135 _ => 135
  | .C136 _ => 136
  | .C137 _ => 137
  | .C138 _ => 138
  | .C139 _ => 139
  | .C140 _ => 140
  | .C141 _ => 141
  | .C142 _ => 142
  | .C143 _ => 143
  | .C144 _ => 144
  | .C145 _ => 145
  | .C146 _ => 146
  | .C147 _ => 147
  | .C148 _ => 148
  | .C149 _ => 149
  | .C150 _ => 150
  | .C151 _ => 151
  | .C152 _ => 152
  | .C153 _ => 153
  | .C154 _ => 154
  | .C155 _ => 155
  | .C156 _ => 156
  | .C157 _ => 157
  | .C158 _ => 158
  | .C159 _ => 159
  | .C160 _ => 160
  | .C161 _ => 161
  | .C162 _ => 162
  | .C163 _ => 163
  | .C164 _ => 164
  | .C165 _ => 165
  | .C166 _ => 166
  | .C167 _ => 167
  | .C168 _ => 168
  | .C169 _ => 169
  | .C170 _ => 170
  | .C171 _ => 171
  | .C172 _ => 172
  | .C173 _ => 173
  | .C174 _ => 174
  | .C175 _ => 175
  | .C176 _ => 176
  | .C177 _ => 177
  | .C178 _ => 178
  | .C179 _ => 179
  | .C180 _ => 180
  | .C181 _ => 181
  | .C182 _ => 182
  | .C183 _ => 183
  | .C184 _ => 184
  | .C185 _ => 185
  | .C186 _ => 186
  | .C187 _ => 187
  | .C188 _ => 188
  | .C189 _ => 189
  | .C190 _ => 190
  | .C191 _ => 191
  | .C192 _ => 192
  | .C193 _ => 193
  | .C194 _ => 194
  | .C195 _ => 195
  | .C196 _ => 196
  | .C197 _ => 197
  | .C198 _ => 198
  | .C199 _ => 199
  | .C200 _ => 200
  | .C201 _ => 201
  | .C202 _ => 202
  | .C203 _ => 203
  | .C204 _ => 204
  | .C205 _ => 205
  | .C206 _ => 206
  | .C207 _ => 207
  | .C208 _ => 208
  | .C209 _ => 209
  | .C210 _ => 210
  | .C211 _ => 211
  | .C212 _ => 212
  | .C213 _ => 213
  | .C214 _ => 214
  | .C215 _ => 215
  | .C216 _ => 216
  | .C217 _ => 217
  | .C218 _ => 218
  | .C219 _ => 219
  | .C220 _ => 220
  | .C221 _ => 221
  | .C222 _ => 222
  | .C223 _ => 223
  | .C224 _ => 224
  | .C225 _ => 225
  | .C226 _ => 226
  | .C227 _ => 227
  | .C228 _ => 228
  | .C229 _ => 229
  | .C230 _ => 230
  | .C231 _ => 231
  | .C232 _ => 232
  | .C233 _ => 233
  | .C234 _ => 234
  | .C235 _ => 235
  | .C236 _ => 236
  | .C237 _ => 237
  | .C238 _ => 238
  | .C239 _ => 239
  | .C240 _ => 240
  | .C241 _ => 241
  | .C242 _ => 242
  | .C243 _ => 243
  | .C244 _ => 244

/-- Type quantifiers: k_a : Type -/
def last (x : k_a) : (large_variant k_a) :=
  (C244 x)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
