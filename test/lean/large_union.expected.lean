import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace Out

mutual
inductive large_variant_chunk0  where
  | C0 (_ : Int)
  | C1 (_ : Int)
  | C2 (_ : Int)
  | C3 (_ : Int)
  | C4 (_ : Int)
  | C5 (_ : Int)
  | C6 (_ : Int)
  | C7 (_ : Int)
  | C8 (_ : Int)
  | C9 (_ : Int)
  | C10 (_ : Int)
  | C11 (_ : Int)
  | C12 (_ : Int)
  | C13 (_ : Int)
  | C14 (_ : Int)
  | C15 (_ : Int)
  | C16 (_ : Int)
  | C17 (_ : Int)
  | C18 (_ : Int)
  | C19 (_ : Int)
  | C20 (_ : Int)
  | C21 (_ : Int)
  | C22 (_ : Int)
  | C23 (_ : Int)
  | C24 (_ : Int)
  | C25 (_ : Int)
  | C26 (_ : Int)
  | C27 (_ : Int)
  | C28 (_ : Int)
  | C29 (_ : Int)
  | C30 (_ : Int)
  | C31 (_ : Int)
  | C32 (_ : Int)
  | C33 (_ : Int)
  | C34 (_ : Int)
  | C35 (_ : Int)
  | C36 (_ : Int)
  | C37 (_ : Int)
  | C38 (_ : Int)
  | C39 (_ : Int)
  | C40 (_ : Int)
  | C41 (_ : Int)
  | C42 (_ : Int)
  | C43 (_ : Int)
  | C44 (_ : Int)
  | C45 (_ : Int)
  | C46 (_ : Int)
  | C47 (_ : Int)
  | C48 (_ : Int)
  | C49 (_ : Int)
  | C50 (_ : Int)
  | C51 (_ : Int)
  | C52 (_ : Int)
  | C53 (_ : Int)
  | C54 (_ : Int)
  | C55 (_ : Int)
  | C56 (_ : Int)
  | C57 (_ : Int)
  | C58 (_ : Int)
  | C59 (_ : Int)
  | C60 (_ : Int)
  | C61 (_ : Int)
  | C62 (_ : Int)
  | C63 (_ : Int)
  | C64 (_ : Int)
  | C65 (_ : Int)
  | C66 (_ : Int)
  | C67 (_ : Int)
  | C68 (_ : Int)
  | C69 (_ : Int)
  | C70 (_ : Int)
  | C71 (_ : Int)
  | C72 (_ : Int)
  | C73 (_ : Int)
  | C74 (_ : Int)
  | C75 (_ : Int)
  | C76 (_ : Int)
  | C77 (_ : Int)
  | C78 (_ : Int)
  | C79 (_ : Int)
  | C80 (_ : Int)
  | C81 (_ : Int)
  | C82 (_ : Int)
  | C83 (_ : Int)
  | C84 (_ : Int)
  | C85 (_ : Int)
  | C86 (_ : Int)
  | C87 (_ : Int)
  | C88 (_ : Int)
  | C89 (_ : Int)
  | C90 (_ : Int)
  | C91 (_ : Int)
  | C92 (_ : Int)
  | C93 (_ : Int)
  | C94 (_ : Int)
  | C95 (_ : Int)
  | C96 (_ : Int)
  | C97 (_ : Int)
  | C98 (_ : Int)
  | C99 (_ : Int)
  | C100 (_ : Int)
  | C101 (_ : Int)
  | C102 (_ : Int)
  | C103 (_ : Int)
  | C104 (_ : Int)
  | C105 (_ : Int)
  | C106 (_ : Int)
  | C107 (_ : Int)
  | C108 (_ : Int)
  | C109 (_ : Int)
  | C110 (_ : Int)
  | C111 (_ : Int)
  | C112 (_ : Int)
  | C113 (_ : Int)
  | C114 (_ : Int)
  | C115 (_ : Int)
  | C116 (_ : Int)
  | C117 (_ : Int)
  | C118 (_ : Int)
  | C119 (_ : Int)
  | C120 (_ : Int)
  | C121 (_ : Int)
  | C122 (_ : Int)
  | C123 (_ : Int)
  | C124 (_ : Int)
  | C125 (_ : Int)
  | C126 (_ : Int)
  | C127 (_ : Int)
  | C128 (_ : Int)
  | C129 (_ : Int)
  | C130 (_ : Int)
  | C131 (_ : Int)
  | C132 (_ : Int)
  | C133 (_ : Int)
  | C134 (_ : Int)
  | C135 (_ : Int)
  | C136 (_ : Int)
  | C137 (_ : Int)
  | C138 (_ : Int)
  | C139 (_ : Int)
  | C140 (_ : Int)
  | C141 (_ : Int)
  | C142 (_ : Int)
  | C143 (_ : Int)
  | C144 (_ : Int)
  | C145 (_ : Int)
  | C146 (_ : Int)
  | C147 (_ : Int)
  | C148 (_ : Int)
  | C149 (_ : Int)
  | C150 (_ : Int)
  | C151 (_ : Int)
  | C152 (_ : Int)
  | C153 (_ : Int)
  | C154 (_ : Int)
  | C155 (_ : Int)
  | C156 (_ : Int)
  | C157 (_ : Int)
  | C158 (_ : Int)
  | C159 (_ : Int)
  | C160 (_ : Int)
  | C161 (_ : Int)
  | C162 (_ : Int)
  | C163 (_ : Int)
  | C164 (_ : Int)
  | C165 (_ : Int)
  | C166 (_ : Int)
  | C167 (_ : Int)
  | C168 (_ : Int)
  | C169 (_ : Int)
  | C170 (_ : Int)
  | C171 (_ : Int)
  | C172 (_ : Int)
  | C173 (_ : Int)
  | C174 (_ : Int)
  | C175 (_ : Int)
  | C176 (_ : Int)
  | C177 (_ : Int)
  | C178 (_ : Int)
  | C179 (_ : Int)
  | C180 (_ : Int)
  | C181 (_ : Int)
  | C182 (_ : Int)
  | C183 (_ : Int)
  | C184 (_ : Int)
  | C185 (_ : Int)
  | C186 (_ : Int)
  | C187 (_ : Int)
  | C188 (_ : Int)
  | C189 (_ : Int)
  | C190 (_ : Int)
  | C191 (_ : Int)
  | C192 (_ : Int)
  | C193 (_ : Int)
  | C194 (_ : Int)
  | C195 (_ : Int)
  | C196 (_ : Int)
  | C197 (_ : Int)
  | C198 (_ : Int)
  | C199 (_ : Int)
  | C200 (_ : Int)
  | C201 (_ : Int)
  | C202 (_ : Int)
  | C203 (_ : Int)
  | C204 (_ : Int)
  | C205 (_ : Int)
  | C206 (_ : Int)
  | C207 (_ : Int)
  | C208 (_ : Int)
  | C209 (_ : Int)
  | C210 (_ : Int)
  | C211 (_ : Int)
  | C212 (_ : Int)
  | C213 (_ : Int)
  | C214 (_ : Int)
  | C215 (_ : Int)
  | C216 (_ : Int)
  | C217 (_ : Int)
  | C218 (_ : Int)
  | C219 (_ : Int)
  | C220 (_ : Int)
  | C221 (_ : Int)
  | C222 (_ : Int)
  | C223 (_ : Int)
  | C224 (_ : Int)
  | C225 (_ : Int)
  | C226 (_ : Int)
  | C227 (_ : Int)
  | C228 (_ : Int)
  | C229 (_ : Int)
  | C230 (_ : Int)
  | C231 (_ : Int)
  | C232 (_ : Int)
  | C233 (_ : Int)
  | C234 (_ : Int)
  | C235 (_ : Int)
  | C236 (_ : Int)
  | C237 (_ : Int)
  | C238 (_ : Int)
  | C239 (_ : Int)
  | C240 (_ : Int)
  | C241 (_ : Int)
  | C242 (_ : Int)
  | C243 (_ : Int)
  deriving Inhabited, BEq, Repr
inductive large_variant_chunk1  where
  | C244 (_ : Int)
  deriving Inhabited, BEq, Repr
inductive large_variant  where
  | chunk0 (_ : (large_variant_chunk0 ))
  | chunk1 (_ : (large_variant_chunk1 ))
  deriving Inhabited, BEq, Repr
end
@[match_pattern] abbrev large_variant.C0  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C0 x)
@[match_pattern] abbrev large_variant.C1  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C1 x)
@[match_pattern] abbrev large_variant.C2  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C2 x)
@[match_pattern] abbrev large_variant.C3  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C3 x)
@[match_pattern] abbrev large_variant.C4  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C4 x)
@[match_pattern] abbrev large_variant.C5  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C5 x)
@[match_pattern] abbrev large_variant.C6  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C6 x)
@[match_pattern] abbrev large_variant.C7  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C7 x)
@[match_pattern] abbrev large_variant.C8  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C8 x)
@[match_pattern] abbrev large_variant.C9  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C9 x)
@[match_pattern] abbrev large_variant.C10  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C10 x)
@[match_pattern] abbrev large_variant.C11  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C11 x)
@[match_pattern] abbrev large_variant.C12  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C12 x)
@[match_pattern] abbrev large_variant.C13  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C13 x)
@[match_pattern] abbrev large_variant.C14  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C14 x)
@[match_pattern] abbrev large_variant.C15  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C15 x)
@[match_pattern] abbrev large_variant.C16  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C16 x)
@[match_pattern] abbrev large_variant.C17  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C17 x)
@[match_pattern] abbrev large_variant.C18  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C18 x)
@[match_pattern] abbrev large_variant.C19  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C19 x)
@[match_pattern] abbrev large_variant.C20  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C20 x)
@[match_pattern] abbrev large_variant.C21  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C21 x)
@[match_pattern] abbrev large_variant.C22  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C22 x)
@[match_pattern] abbrev large_variant.C23  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C23 x)
@[match_pattern] abbrev large_variant.C24  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C24 x)
@[match_pattern] abbrev large_variant.C25  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C25 x)
@[match_pattern] abbrev large_variant.C26  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C26 x)
@[match_pattern] abbrev large_variant.C27  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C27 x)
@[match_pattern] abbrev large_variant.C28  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C28 x)
@[match_pattern] abbrev large_variant.C29  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C29 x)
@[match_pattern] abbrev large_variant.C30  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C30 x)
@[match_pattern] abbrev large_variant.C31  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C31 x)
@[match_pattern] abbrev large_variant.C32  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C32 x)
@[match_pattern] abbrev large_variant.C33  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C33 x)
@[match_pattern] abbrev large_variant.C34  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C34 x)
@[match_pattern] abbrev large_variant.C35  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C35 x)
@[match_pattern] abbrev large_variant.C36  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C36 x)
@[match_pattern] abbrev large_variant.C37  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C37 x)
@[match_pattern] abbrev large_variant.C38  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C38 x)
@[match_pattern] abbrev large_variant.C39  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C39 x)
@[match_pattern] abbrev large_variant.C40  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C40 x)
@[match_pattern] abbrev large_variant.C41  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C41 x)
@[match_pattern] abbrev large_variant.C42  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C42 x)
@[match_pattern] abbrev large_variant.C43  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C43 x)
@[match_pattern] abbrev large_variant.C44  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C44 x)
@[match_pattern] abbrev large_variant.C45  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C45 x)
@[match_pattern] abbrev large_variant.C46  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C46 x)
@[match_pattern] abbrev large_variant.C47  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C47 x)
@[match_pattern] abbrev large_variant.C48  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C48 x)
@[match_pattern] abbrev large_variant.C49  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C49 x)
@[match_pattern] abbrev large_variant.C50  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C50 x)
@[match_pattern] abbrev large_variant.C51  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C51 x)
@[match_pattern] abbrev large_variant.C52  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C52 x)
@[match_pattern] abbrev large_variant.C53  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C53 x)
@[match_pattern] abbrev large_variant.C54  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C54 x)
@[match_pattern] abbrev large_variant.C55  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C55 x)
@[match_pattern] abbrev large_variant.C56  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C56 x)
@[match_pattern] abbrev large_variant.C57  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C57 x)
@[match_pattern] abbrev large_variant.C58  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C58 x)
@[match_pattern] abbrev large_variant.C59  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C59 x)
@[match_pattern] abbrev large_variant.C60  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C60 x)
@[match_pattern] abbrev large_variant.C61  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C61 x)
@[match_pattern] abbrev large_variant.C62  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C62 x)
@[match_pattern] abbrev large_variant.C63  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C63 x)
@[match_pattern] abbrev large_variant.C64  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C64 x)
@[match_pattern] abbrev large_variant.C65  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C65 x)
@[match_pattern] abbrev large_variant.C66  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C66 x)
@[match_pattern] abbrev large_variant.C67  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C67 x)
@[match_pattern] abbrev large_variant.C68  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C68 x)
@[match_pattern] abbrev large_variant.C69  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C69 x)
@[match_pattern] abbrev large_variant.C70  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C70 x)
@[match_pattern] abbrev large_variant.C71  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C71 x)
@[match_pattern] abbrev large_variant.C72  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C72 x)
@[match_pattern] abbrev large_variant.C73  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C73 x)
@[match_pattern] abbrev large_variant.C74  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C74 x)
@[match_pattern] abbrev large_variant.C75  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C75 x)
@[match_pattern] abbrev large_variant.C76  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C76 x)
@[match_pattern] abbrev large_variant.C77  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C77 x)
@[match_pattern] abbrev large_variant.C78  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C78 x)
@[match_pattern] abbrev large_variant.C79  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C79 x)
@[match_pattern] abbrev large_variant.C80  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C80 x)
@[match_pattern] abbrev large_variant.C81  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C81 x)
@[match_pattern] abbrev large_variant.C82  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C82 x)
@[match_pattern] abbrev large_variant.C83  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C83 x)
@[match_pattern] abbrev large_variant.C84  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C84 x)
@[match_pattern] abbrev large_variant.C85  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C85 x)
@[match_pattern] abbrev large_variant.C86  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C86 x)
@[match_pattern] abbrev large_variant.C87  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C87 x)
@[match_pattern] abbrev large_variant.C88  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C88 x)
@[match_pattern] abbrev large_variant.C89  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C89 x)
@[match_pattern] abbrev large_variant.C90  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C90 x)
@[match_pattern] abbrev large_variant.C91  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C91 x)
@[match_pattern] abbrev large_variant.C92  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C92 x)
@[match_pattern] abbrev large_variant.C93  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C93 x)
@[match_pattern] abbrev large_variant.C94  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C94 x)
@[match_pattern] abbrev large_variant.C95  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C95 x)
@[match_pattern] abbrev large_variant.C96  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C96 x)
@[match_pattern] abbrev large_variant.C97  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C97 x)
@[match_pattern] abbrev large_variant.C98  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C98 x)
@[match_pattern] abbrev large_variant.C99  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C99 x)
@[match_pattern] abbrev large_variant.C100  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C100 x)
@[match_pattern] abbrev large_variant.C101  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C101 x)
@[match_pattern] abbrev large_variant.C102  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C102 x)
@[match_pattern] abbrev large_variant.C103  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C103 x)
@[match_pattern] abbrev large_variant.C104  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C104 x)
@[match_pattern] abbrev large_variant.C105  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C105 x)
@[match_pattern] abbrev large_variant.C106  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C106 x)
@[match_pattern] abbrev large_variant.C107  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C107 x)
@[match_pattern] abbrev large_variant.C108  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C108 x)
@[match_pattern] abbrev large_variant.C109  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C109 x)
@[match_pattern] abbrev large_variant.C110  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C110 x)
@[match_pattern] abbrev large_variant.C111  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C111 x)
@[match_pattern] abbrev large_variant.C112  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C112 x)
@[match_pattern] abbrev large_variant.C113  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C113 x)
@[match_pattern] abbrev large_variant.C114  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C114 x)
@[match_pattern] abbrev large_variant.C115  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C115 x)
@[match_pattern] abbrev large_variant.C116  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C116 x)
@[match_pattern] abbrev large_variant.C117  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C117 x)
@[match_pattern] abbrev large_variant.C118  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C118 x)
@[match_pattern] abbrev large_variant.C119  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C119 x)
@[match_pattern] abbrev large_variant.C120  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C120 x)
@[match_pattern] abbrev large_variant.C121  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C121 x)
@[match_pattern] abbrev large_variant.C122  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C122 x)
@[match_pattern] abbrev large_variant.C123  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C123 x)
@[match_pattern] abbrev large_variant.C124  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C124 x)
@[match_pattern] abbrev large_variant.C125  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C125 x)
@[match_pattern] abbrev large_variant.C126  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C126 x)
@[match_pattern] abbrev large_variant.C127  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C127 x)
@[match_pattern] abbrev large_variant.C128  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C128 x)
@[match_pattern] abbrev large_variant.C129  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C129 x)
@[match_pattern] abbrev large_variant.C130  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C130 x)
@[match_pattern] abbrev large_variant.C131  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C131 x)
@[match_pattern] abbrev large_variant.C132  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C132 x)
@[match_pattern] abbrev large_variant.C133  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C133 x)
@[match_pattern] abbrev large_variant.C134  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C134 x)
@[match_pattern] abbrev large_variant.C135  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C135 x)
@[match_pattern] abbrev large_variant.C136  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C136 x)
@[match_pattern] abbrev large_variant.C137  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C137 x)
@[match_pattern] abbrev large_variant.C138  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C138 x)
@[match_pattern] abbrev large_variant.C139  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C139 x)
@[match_pattern] abbrev large_variant.C140  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C140 x)
@[match_pattern] abbrev large_variant.C141  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C141 x)
@[match_pattern] abbrev large_variant.C142  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C142 x)
@[match_pattern] abbrev large_variant.C143  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C143 x)
@[match_pattern] abbrev large_variant.C144  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C144 x)
@[match_pattern] abbrev large_variant.C145  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C145 x)
@[match_pattern] abbrev large_variant.C146  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C146 x)
@[match_pattern] abbrev large_variant.C147  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C147 x)
@[match_pattern] abbrev large_variant.C148  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C148 x)
@[match_pattern] abbrev large_variant.C149  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C149 x)
@[match_pattern] abbrev large_variant.C150  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C150 x)
@[match_pattern] abbrev large_variant.C151  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C151 x)
@[match_pattern] abbrev large_variant.C152  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C152 x)
@[match_pattern] abbrev large_variant.C153  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C153 x)
@[match_pattern] abbrev large_variant.C154  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C154 x)
@[match_pattern] abbrev large_variant.C155  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C155 x)
@[match_pattern] abbrev large_variant.C156  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C156 x)
@[match_pattern] abbrev large_variant.C157  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C157 x)
@[match_pattern] abbrev large_variant.C158  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C158 x)
@[match_pattern] abbrev large_variant.C159  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C159 x)
@[match_pattern] abbrev large_variant.C160  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C160 x)
@[match_pattern] abbrev large_variant.C161  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C161 x)
@[match_pattern] abbrev large_variant.C162  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C162 x)
@[match_pattern] abbrev large_variant.C163  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C163 x)
@[match_pattern] abbrev large_variant.C164  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C164 x)
@[match_pattern] abbrev large_variant.C165  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C165 x)
@[match_pattern] abbrev large_variant.C166  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C166 x)
@[match_pattern] abbrev large_variant.C167  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C167 x)
@[match_pattern] abbrev large_variant.C168  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C168 x)
@[match_pattern] abbrev large_variant.C169  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C169 x)
@[match_pattern] abbrev large_variant.C170  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C170 x)
@[match_pattern] abbrev large_variant.C171  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C171 x)
@[match_pattern] abbrev large_variant.C172  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C172 x)
@[match_pattern] abbrev large_variant.C173  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C173 x)
@[match_pattern] abbrev large_variant.C174  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C174 x)
@[match_pattern] abbrev large_variant.C175  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C175 x)
@[match_pattern] abbrev large_variant.C176  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C176 x)
@[match_pattern] abbrev large_variant.C177  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C177 x)
@[match_pattern] abbrev large_variant.C178  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C178 x)
@[match_pattern] abbrev large_variant.C179  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C179 x)
@[match_pattern] abbrev large_variant.C180  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C180 x)
@[match_pattern] abbrev large_variant.C181  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C181 x)
@[match_pattern] abbrev large_variant.C182  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C182 x)
@[match_pattern] abbrev large_variant.C183  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C183 x)
@[match_pattern] abbrev large_variant.C184  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C184 x)
@[match_pattern] abbrev large_variant.C185  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C185 x)
@[match_pattern] abbrev large_variant.C186  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C186 x)
@[match_pattern] abbrev large_variant.C187  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C187 x)
@[match_pattern] abbrev large_variant.C188  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C188 x)
@[match_pattern] abbrev large_variant.C189  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C189 x)
@[match_pattern] abbrev large_variant.C190  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C190 x)
@[match_pattern] abbrev large_variant.C191  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C191 x)
@[match_pattern] abbrev large_variant.C192  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C192 x)
@[match_pattern] abbrev large_variant.C193  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C193 x)
@[match_pattern] abbrev large_variant.C194  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C194 x)
@[match_pattern] abbrev large_variant.C195  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C195 x)
@[match_pattern] abbrev large_variant.C196  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C196 x)
@[match_pattern] abbrev large_variant.C197  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C197 x)
@[match_pattern] abbrev large_variant.C198  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C198 x)
@[match_pattern] abbrev large_variant.C199  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C199 x)
@[match_pattern] abbrev large_variant.C200  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C200 x)
@[match_pattern] abbrev large_variant.C201  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C201 x)
@[match_pattern] abbrev large_variant.C202  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C202 x)
@[match_pattern] abbrev large_variant.C203  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C203 x)
@[match_pattern] abbrev large_variant.C204  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C204 x)
@[match_pattern] abbrev large_variant.C205  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C205 x)
@[match_pattern] abbrev large_variant.C206  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C206 x)
@[match_pattern] abbrev large_variant.C207  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C207 x)
@[match_pattern] abbrev large_variant.C208  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C208 x)
@[match_pattern] abbrev large_variant.C209  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C209 x)
@[match_pattern] abbrev large_variant.C210  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C210 x)
@[match_pattern] abbrev large_variant.C211  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C211 x)
@[match_pattern] abbrev large_variant.C212  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C212 x)
@[match_pattern] abbrev large_variant.C213  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C213 x)
@[match_pattern] abbrev large_variant.C214  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C214 x)
@[match_pattern] abbrev large_variant.C215  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C215 x)
@[match_pattern] abbrev large_variant.C216  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C216 x)
@[match_pattern] abbrev large_variant.C217  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C217 x)
@[match_pattern] abbrev large_variant.C218  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C218 x)
@[match_pattern] abbrev large_variant.C219  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C219 x)
@[match_pattern] abbrev large_variant.C220  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C220 x)
@[match_pattern] abbrev large_variant.C221  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C221 x)
@[match_pattern] abbrev large_variant.C222  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C222 x)
@[match_pattern] abbrev large_variant.C223  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C223 x)
@[match_pattern] abbrev large_variant.C224  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C224 x)
@[match_pattern] abbrev large_variant.C225  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C225 x)
@[match_pattern] abbrev large_variant.C226  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C226 x)
@[match_pattern] abbrev large_variant.C227  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C227 x)
@[match_pattern] abbrev large_variant.C228  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C228 x)
@[match_pattern] abbrev large_variant.C229  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C229 x)
@[match_pattern] abbrev large_variant.C230  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C230 x)
@[match_pattern] abbrev large_variant.C231  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C231 x)
@[match_pattern] abbrev large_variant.C232  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C232 x)
@[match_pattern] abbrev large_variant.C233  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C233 x)
@[match_pattern] abbrev large_variant.C234  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C234 x)
@[match_pattern] abbrev large_variant.C235  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C235 x)
@[match_pattern] abbrev large_variant.C236  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C236 x)
@[match_pattern] abbrev large_variant.C237  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C237 x)
@[match_pattern] abbrev large_variant.C238  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C238 x)
@[match_pattern] abbrev large_variant.C239  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C239 x)
@[match_pattern] abbrev large_variant.C240  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C240 x)
@[match_pattern] abbrev large_variant.C241  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C241 x)
@[match_pattern] abbrev large_variant.C242  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C242 x)
@[match_pattern] abbrev large_variant.C243  (x : Int) : large_variant  := large_variant.chunk0 (large_variant_chunk0.C243 x)
@[match_pattern] abbrev large_variant.C244  (x : Int) : large_variant  := large_variant.chunk1 (large_variant_chunk1.C244 x)
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

def tag (x : large_variant) : Int :=
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

/-- Type quantifiers: x : Int -/
def last (x : Int) : large_variant :=
  (C244 x)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
