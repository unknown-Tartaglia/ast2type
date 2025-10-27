from tree_sitter import Node

def has_error(node: Node) -> bool:
    if node.type == 'ERROR':
        return True
    for n in node.children:
        ret = has_error(n)
        if ret:
            return True
    return False

def has_named_child(node: Node, name: str) -> bool:
    if node.child_by_field_name(name) is None:
        return False
    else: return True