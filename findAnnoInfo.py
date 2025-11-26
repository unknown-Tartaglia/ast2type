#!/usr/bin/env python3
import json
import sys
import re

if len(sys.argv) != 2:
    print("用法: python3 find_missing_annotations.py <JSON文件路径>")
    print("示例: python3 find_missing_annotations.py output/typeinfo/Air/arg.js.json")
    sys.exit(1)

json_file = sys.argv[1]

# 定义列宽
COLUMN_WIDTHS = {
    "v8kind": 20,
    "morph_kind": 30,
    "context": 80,
    "location": 50,
    "pos": 8,
    "file": 50
}

def format_row(kind, morph_kind, context, location, pos, file):
    """格式化一行数据，使用固定列宽"""
    return (f"{kind:<{COLUMN_WIDTHS['v8kind']}} "
            f"{morph_kind:<{COLUMN_WIDTHS['morph_kind']}} "
            f"{context:<{COLUMN_WIDTHS['context']}} "
            f"{location:<{COLUMN_WIDTHS['location']}} "
            f"{pos:<{COLUMN_WIDTHS['pos']}} "
            f"{file:<{COLUMN_WIDTHS['file']}}")

try:
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    # 输出表头
    print(format_row("v8kind", "morph_kind", "上下文", "具体位置", "pos", "file"))
    
    # 分隔线
    separator = "-" * (sum(COLUMN_WIDTHS.values()) + len(COLUMN_WIDTHS) - 1)
    print(separator)
    
    # 读取标准输入
    for line in sys.stdin:
        line = line.strip()
        # 使用正则表达式提取位置和节点类型
        match = re.search(r'Omitted type annotation at position (\d+) with NodeType ([A-Za-z]+)', line)
        if match:
            position = int(match.group(1))
            node_type = match.group(2)
            
            # 查找匹配的条目
            found = False
            for item in data:
                if item.get('location') == position and item.get('exprKind') == node_type:
                    kind = item.get('exprKind', 'Unknown')
                    morph_kind = item.get('morphKind', 'Unknown')  # 获取 morph_kind，如果没有则使用 'Unknown'
                    context = item.get('context', '')
                    location = item.get('exprText', '')
                    pos = item.get('location', '')
                    print(format_row(kind, morph_kind, context, location, pos, json_file))
                    found = True
                    break
            
            # 如果没有找到匹配项，输出占位符
            if not found:
                # 使用更长的占位符确保列宽一致
                context_placeholder = "-" * (COLUMN_WIDTHS['context'] - 2)
                location_placeholder = "-" * (COLUMN_WIDTHS['location'] - 2)
                morph_kind_placeholder = "-" * (COLUMN_WIDTHS['morph_kind'] - 2)
                print(format_row(node_type, morph_kind_placeholder, context_placeholder, location_placeholder, position, json_file))
                
except FileNotFoundError:
    print(f"错误: JSON 文件不存在: {json_file}")
    sys.exit(1)
except json.JSONDecodeError:
    print(f"错误: JSON 文件格式错误: {json_file}")
    sys.exit(1)