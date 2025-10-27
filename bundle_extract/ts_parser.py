from typing import List

import tree_sitter_typescript as tts
from tree_sitter import Parser, Tree, Language
from tree_sitter_utils import has_error

def check_grammar(ts_code: str) -> bool:
    """
    Check if the provided TS code has syntax errors using the tree-sitter TS parser.

    :param TS: The TS code to be checked for grammar errors.
    :type ts_code: str

    :return: True if there are syntax errors in the code, False otherwise.
    :rtype: bool
    """
    TS_LANGUAGE = Language(tts.language_typescript())
    parser = Parser(TS_LANGUAGE)
    tree = parser.parse(ts_code.encode(), encoding="utf8")
    return has_error(tree.root_node)

def parse_ts(ts_code: str) -> Tree:
    """
    Parse the provided TS code into an abstract syntax tree (AST).

    :param ts_code: The TS code to be parsed.
    :type ts_code: str

    :return: The abstract syntax tree representing the parsed TS code.
    :rtype: Tree
    """
    TS_LANGUAGE = Language(tts.language_typescript())
    parser = Parser(TS_LANGUAGE)
    tree = parser.parse(ts_code.encode(), encoding="utf8")
    return tree
