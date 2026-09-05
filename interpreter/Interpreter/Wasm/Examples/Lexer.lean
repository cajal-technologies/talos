import Interpreter.Wasm.Decoder.Wat

/-! Kernel checks for comment boundaries, quoting, and malformed parentheses. -/
namespace Wasm.Decoder.Wat

set_option maxRecDepth 10000

theorem lexer_nested_comments :
    parseAll "(module (; outer (; inner ;) end ;) (func))" =
      .ok [.list [.atom "module", .list [.atom "func"]]] := rfl

theorem lexer_line_comments :
    parseAll "(module ;; ignored ( )\n (func))" =
      .ok [.list [.atom "module", .list [.atom "func"]]] := rfl

theorem lexer_quoted_comment_markers :
    parseAll "(data \"(;literal;) ;; literal\")" =
      .ok [.list [.atom "data", .atom "\"(;literal;) ;; literal\""]] := rfl

theorem lexer_escaped_quote :
    parseAll "(data \"a\\\"b\")" =
      .ok [.list [.atom "data", .atom "\"a\\\"b\""]] := rfl

theorem lexer_unbalanced_parentheses :
    parseAll "(module" = .error "unbalanced parens: missing ')'" ∧
    parseAll "module)" = .error "unexpected ')'" := ⟨rfl, rfl⟩

end Wasm.Decoder.Wat
