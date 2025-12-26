/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0 */

#include "../include/formal_proof_circuits.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/**
 * @file fopl_parser.c
 * @brief Parse First-Order Predicate Logic formulas into AST
 * 
 * Grammar:
 * Formula ::= Atom | UnaryOp Formula | Formula BinaryOp Formula | Quantifier Var . Formula
 * Atom ::= Predicate(Terms) | Term = Term | Term < Term | Term > Term | (Formula)
 * UnaryOp ::= ¬ | NOT
 * BinaryOp ::= ∧ | AND | ∨ | OR | → | -> | ↔ | <-> | ⊕ | XOR
 * Quantifier ::= ∀ | FORALL | ∃ | EXISTS
 * Term ::= Var | Function(Terms) | Constant
 */

typedef struct {
    const char* input;
    int pos;
    int len;
} parser_state_t;

// Token types
typedef enum {
    TOK_EOF,
    TOK_LPAREN,
    TOK_RPAREN,
    TOK_DOT,
    TOK_COMMA,
    TOK_NOT,
    TOK_AND,
    TOK_OR,
    TOK_IMPLIES,
    TOK_IFF,
    TOK_XOR,
    TOK_FORALL,
    TOK_EXISTS,
    TOK_EQ,
    TOK_LT,
    TOK_GT,
    TOK_IDENT,
    TOK_NUMBER
} token_type_t;

typedef struct {
    token_type_t type;
    char* value;
} token_t;

// Forward declarations
static logic_node_t* parse_formula(parser_state_t* state);
static logic_node_t* parse_atom(parser_state_t* state);
static token_t next_token(parser_state_t* state);
static void consume_whitespace(parser_state_t* state);

// Create a new logic node
static logic_node_t* create_node(logic_node_type_t type) {
    logic_node_t* node = calloc(1, sizeof(logic_node_t));
    node->type = type;
    return node;
}

// Create a binary operation node
static logic_node_t* create_binary_op(logic_node_type_t type, logic_node_t* left, logic_node_t* right) {
    logic_node_t* node = create_node(type);
    node->left = left;
    node->right = right;
    return node;
}

// Create a unary operation node
static logic_node_t* create_unary_op(logic_node_type_t type, logic_node_t* child) {
    logic_node_t* node = create_node(type);
    node->left = child;
    return node;
}

// Skip whitespace
static void consume_whitespace(parser_state_t* state) {
    while (state->pos < state->len && isspace(state->input[state->pos])) {
        state->pos++;
    }
}

// Peek at next character
static char peek_char(parser_state_t* state) {
    consume_whitespace(state);
    if (state->pos >= state->len) return '\0';
    return state->input[state->pos];
}

// Consume a character
static char next_char(parser_state_t* state) {
    consume_whitespace(state);
    if (state->pos >= state->len) return '\0';
    return state->input[state->pos++];
}

// Check if character starts an identifier
static bool is_ident_start(char c) {
    return isalpha(c) || c == '_';
}

// Check if character continues an identifier
static bool is_ident_cont(char c) {
    return isalnum(c) || c == '_' || c == '\'';
}

// Parse identifier or keyword
static token_t parse_ident(parser_state_t* state) {
    int start = state->pos;
    while (state->pos < state->len && is_ident_cont(state->input[state->pos])) {
        state->pos++;
    }
    
    int len = state->pos - start;
    char* value = malloc(len + 1);
    memcpy(value, state->input + start, len);
    value[len] = '\0';
    
    token_t tok = {.value = value};
    
    // Check for keywords
    if (strcmp(value, "NOT") == 0 || strcmp(value, "¬") == 0) {
        tok.type = TOK_NOT;
    } else if (strcmp(value, "AND") == 0) {
        tok.type = TOK_AND;
    } else if (strcmp(value, "OR") == 0) {
        tok.type = TOK_OR;
    } else if (strcmp(value, "IMPLIES") == 0) {
        tok.type = TOK_IMPLIES;
    } else if (strcmp(value, "IFF") == 0) {
        tok.type = TOK_IFF;
    } else if (strcmp(value, "XOR") == 0) {
        tok.type = TOK_XOR;
    } else if (strcmp(value, "FORALL") == 0) {
        tok.type = TOK_FORALL;
    } else if (strcmp(value, "EXISTS") == 0) {
        tok.type = TOK_EXISTS;
    } else {
        tok.type = TOK_IDENT;
    }
    
    return tok;
}

// Get next token
static token_t next_token(parser_state_t* state) {
    consume_whitespace(state);
    
    if (state->pos >= state->len) {
        return (token_t){TOK_EOF, NULL};
    }
    
    char c = state->input[state->pos];
    
    // Single character tokens
    switch (c) {
        case '(':
            state->pos++;
            return (token_t){TOK_LPAREN, NULL};
        case ')':
            state->pos++;
            return (token_t){TOK_RPAREN, NULL};
        case '.':
            state->pos++;
            return (token_t){TOK_DOT, NULL};
        case ',':
            state->pos++;
            return (token_t){TOK_COMMA, NULL};
        case '=':
            state->pos++;
            return (token_t){TOK_EQ, NULL};
        case '<':
            state->pos++;
            if (state->pos < state->len && state->input[state->pos] == '-') {
                state->pos++;
                if (state->pos < state->len && state->input[state->pos] == '>') {
                    state->pos++;
                    return (token_t){TOK_IFF, NULL};
                }
                state->pos--; // Backtrack
            }
            return (token_t){TOK_LT, NULL};
        case '>':
            state->pos++;
            return (token_t){TOK_GT, NULL};
        case '-':
            if (state->pos + 1 < state->len && state->input[state->pos + 1] == '>') {
                state->pos += 2;
                return (token_t){TOK_IMPLIES, NULL};
            }
            break;
    }
    
    // Unicode symbols
    if ((unsigned char)c >= 0x80) {
        // Simple UTF-8 handling for common symbols
        if (state->pos + 2 < state->len) {
            unsigned char c1 = state->input[state->pos];
            unsigned char c2 = state->input[state->pos + 1];
            unsigned char c3 = state->input[state->pos + 2];
            
            // ¬ (NOT)
            if (c1 == 0xC2 && c2 == 0xAC) {
                state->pos += 2;
                return (token_t){TOK_NOT, NULL};
            }
            // ∧ (AND)
            if (c1 == 0xE2 && c2 == 0x88 && c3 == 0xA7) {
                state->pos += 3;
                return (token_t){TOK_AND, NULL};
            }
            // ∨ (OR)
            if (c1 == 0xE2 && c2 == 0x88 && c3 == 0xA8) {
                state->pos += 3;
                return (token_t){TOK_OR, NULL};
            }
            // → (IMPLIES)
            if (c1 == 0xE2 && c2 == 0x86 && c3 == 0x92) {
                state->pos += 3;
                return (token_t){TOK_IMPLIES, NULL};
            }
            // ↔ (IFF)
            if (c1 == 0xE2 && c2 == 0x86 && c3 == 0x94) {
                state->pos += 3;
                return (token_t){TOK_IFF, NULL};
            }
            // ∀ (FORALL)
            if (c1 == 0xE2 && c2 == 0x88 && c3 == 0x80) {
                state->pos += 3;
                return (token_t){TOK_FORALL, NULL};
            }
            // ∃ (EXISTS)
            if (c1 == 0xE2 && c2 == 0x88 && c3 == 0x83) {
                state->pos += 3;
                return (token_t){TOK_EXISTS, NULL};
            }
            // ⊕ (XOR)
            if (c1 == 0xE2 && c2 == 0x8A && c3 == 0x95) {
                state->pos += 3;
                return (token_t){TOK_XOR, NULL};
            }
        }
    }
    
    // Identifiers and numbers
    if (is_ident_start(c)) {
        return parse_ident(state);
    }
    
    if (isdigit(c)) {
        int start = state->pos;
        while (state->pos < state->len && isdigit(state->input[state->pos])) {
            state->pos++;
        }
        int len = state->pos - start;
        char* value = malloc(len + 1);
        memcpy(value, state->input + start, len);
        value[len] = '\0';
        return (token_t){TOK_NUMBER, value};
    }
    
    // Operators as identifiers
    if (c == '&' || c == '|' || c == '!' || c == '~') {
        char* op = malloc(2);
        op[0] = c;
        op[1] = '\0';
        state->pos++;
        
        if (c == '&') return (token_t){TOK_AND, op};
        if (c == '|') return (token_t){TOK_OR, op};
        if (c == '!' || c == '~') return (token_t){TOK_NOT, op};
    }
    
    // Unknown character
    state->pos++;
    return (token_t){TOK_EOF, NULL};
}

// Peek at next token without consuming
static token_t peek_token(parser_state_t* state) {
    int saved_pos = state->pos;
    token_t tok = next_token(state);
    state->pos = saved_pos;
    return tok;
}

// Parse atomic formula
static logic_node_t* parse_atom(parser_state_t* state) {
    token_t tok = peek_token(state);
    
    // Parenthesized formula
    if (tok.type == TOK_LPAREN) {
        next_token(state); // consume (
        logic_node_t* formula = parse_formula(state);
        tok = next_token(state);
        if (tok.type != TOK_RPAREN) {
            fprintf(stderr, "Expected ')'\n");
            return NULL;
        }
        return formula;
    }
    
    // Identifier (predicate or variable)
    if (tok.type == TOK_IDENT) {
        tok = next_token(state);
        char* name = tok.value;
        
        // Check if it's a predicate (followed by '(')
        token_t next = peek_token(state);
        if (next.type == TOK_LPAREN) {
            next_token(state); // consume (
            
            logic_node_t* pred = create_node(LOGIC_PRED);
            pred->name = name;
            
            // Parse arguments
            logic_node_t** args = NULL;
            int num_args = 0;
            
            if (peek_token(state).type != TOK_RPAREN) {
                do {
                    if (peek_token(state).type == TOK_COMMA) {
                        next_token(state); // consume comma
                    }
                    
                    // For now, just parse identifiers as arguments
                    token_t arg_tok = next_token(state);
                    if (arg_tok.type != TOK_IDENT && arg_tok.type != TOK_NUMBER) {
                        fprintf(stderr, "Expected identifier or number in predicate arguments\n");
                        return NULL;
                    }
                    
                    logic_node_t* arg = create_node(LOGIC_VAR);
                    arg->name = arg_tok.value;
                    
                    args = realloc(args, (num_args + 1) * sizeof(logic_node_t*));
                    args[num_args++] = arg;
                    
                } while (peek_token(state).type == TOK_COMMA);
            }
            
            tok = next_token(state);
            if (tok.type != TOK_RPAREN) {
                fprintf(stderr, "Expected ')' after predicate arguments\n");
                return NULL;
            }
            
            pred->args = args;
            pred->arity = num_args;
            return pred;
        }
        
        // It's a variable
        logic_node_t* var = create_node(LOGIC_VAR);
        var->name = name;
        return var;
    }
    
    fprintf(stderr, "Expected atom\n");
    return NULL;
}

// Parse unary formula
static logic_node_t* parse_unary(parser_state_t* state) {
    token_t tok = peek_token(state);
    
    if (tok.type == TOK_NOT) {
        next_token(state); // consume NOT
        logic_node_t* child = parse_unary(state);
        return create_unary_op(LOGIC_NOT, child);
    }
    
    return parse_atom(state);
}

// Parse binary formula with precedence
static logic_node_t* parse_binary(parser_state_t* state, int min_prec) {
    logic_node_t* left = parse_unary(state);
    if (!left) return NULL;
    
    while (1) {
        token_t op = peek_token(state);
        
        // Get operator precedence
        int prec = 0;
        logic_node_type_t op_type = LOGIC_AND;
        
        switch (op.type) {
            case TOK_AND:
                prec = 3;
                op_type = LOGIC_AND;
                break;
            case TOK_OR:
                prec = 2;
                op_type = LOGIC_OR;
                break;
            case TOK_XOR:
                prec = 2;
                op_type = LOGIC_XOR;
                break;
            case TOK_IMPLIES:
                prec = 1;
                op_type = LOGIC_IMPLIES;
                break;
            case TOK_IFF:
                prec = 1;
                op_type = LOGIC_IFF;
                break;
            case TOK_EQ:
                prec = 4;
                op_type = LOGIC_EQ;
                break;
            case TOK_LT:
                prec = 4;
                op_type = LOGIC_LT;
                break;
            case TOK_GT:
                prec = 4;
                op_type = LOGIC_GT;
                break;
            default:
                return left;
        }
        
        if (prec < min_prec) {
            return left;
        }
        
        next_token(state); // consume operator
        
        // Right associative for implies
        int next_min_prec = (op_type == LOGIC_IMPLIES) ? prec : prec + 1;
        
        logic_node_t* right = parse_binary(state, next_min_prec);
        if (!right) return NULL;
        
        left = create_binary_op(op_type, left, right);
    }
}

// Parse quantified formula
static logic_node_t* parse_quantified(parser_state_t* state) {
    token_t tok = peek_token(state);
    
    if (tok.type == TOK_FORALL || tok.type == TOK_EXISTS) {
        next_token(state); // consume quantifier
        
        logic_node_type_t q_type = (tok.type == TOK_FORALL) ? LOGIC_FORALL : LOGIC_EXISTS;
        
        // Parse variable
        token_t var_tok = next_token(state);
        if (var_tok.type != TOK_IDENT) {
            fprintf(stderr, "Expected variable after quantifier\n");
            return NULL;
        }
        
        // Expect dot
        token_t dot = next_token(state);
        if (dot.type != TOK_DOT) {
            fprintf(stderr, "Expected '.' after quantified variable\n");
            return NULL;
        }
        
        // Parse body
        logic_node_t* body = parse_formula(state);
        if (!body) return NULL;
        
        logic_node_t* quant = create_node(q_type);
        logic_node_t* var = create_node(LOGIC_VAR);
        var->name = var_tok.value;
        
        quant->quantified = var;
        quant->left = body;
        return quant;
    }
    
    return parse_binary(state, 0);
}

// Main parsing function
static logic_node_t* parse_formula(parser_state_t* state) {
    return parse_quantified(state);
}

// Public API
logic_node_t* parse_fopl(const char* formula) {
    parser_state_t state = {
        .input = formula,
        .pos = 0,
        .len = strlen(formula)
    };
    
    logic_node_t* ast = parse_formula(&state);
    
    // Check we consumed everything
    token_t tok = next_token(&state);
    if (tok.type != TOK_EOF) {
        fprintf(stderr, "Unexpected token at end of formula\n");
        // TODO: free AST
        return NULL;
    }
    
    return ast;
}

// Pretty print AST (for debugging)
void print_ast(logic_node_t* node, int indent) {
    if (!node) return;
    
    for (int i = 0; i < indent; i++) printf("  ");
    
    switch (node->type) {
        case LOGIC_VAR:
            printf("VAR(%s)\n", node->name);
            break;
        case LOGIC_NOT:
            printf("NOT\n");
            print_ast(node->left, indent + 1);
            break;
        case LOGIC_AND:
            printf("AND\n");
            print_ast(node->left, indent + 1);
            print_ast(node->right, indent + 1);
            break;
        case LOGIC_OR:
            printf("OR\n");
            print_ast(node->left, indent + 1);
            print_ast(node->right, indent + 1);
            break;
        case LOGIC_IMPLIES:
            printf("IMPLIES\n");
            print_ast(node->left, indent + 1);
            print_ast(node->right, indent + 1);
            break;
        case LOGIC_IFF:
            printf("IFF\n");
            print_ast(node->left, indent + 1);
            print_ast(node->right, indent + 1);
            break;
        case LOGIC_XOR:
            printf("XOR\n");
            print_ast(node->left, indent + 1);
            print_ast(node->right, indent + 1);
            break;
        case LOGIC_FORALL:
            printf("FORALL %s\n", node->quantified->name);
            print_ast(node->left, indent + 1);
            break;
        case LOGIC_EXISTS:
            printf("EXISTS %s\n", node->quantified->name);
            print_ast(node->left, indent + 1);
            break;
        case LOGIC_PRED:
            printf("PRED(%s", node->name);
            if (node->arity > 0) {
                printf(" [");
                for (int i = 0; i < node->arity; i++) {
                    if (i > 0) printf(", ");
                    printf("%s", node->args[i]->name);
                }
                printf("]");
            }
            printf(")\n");
            break;
        case LOGIC_EQ:
            printf("EQ\n");
            print_ast(node->left, indent + 1);
            print_ast(node->right, indent + 1);
            break;
        case LOGIC_LT:
            printf("LT\n");
            print_ast(node->left, indent + 1);
            print_ast(node->right, indent + 1);
            break;
        case LOGIC_GT:
            printf("GT\n");
            print_ast(node->left, indent + 1);
            print_ast(node->right, indent + 1);
            break;
        default:
            printf("UNKNOWN\n");
    }
}