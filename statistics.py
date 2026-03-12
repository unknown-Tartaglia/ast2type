#!/usr/bin/env python3
"""
类型推导结果统计脚本
分析 typeinfo.json 文件，生成统计图表
"""

import json
import os
import sys
from collections import Counter, defaultdict
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path

def load_typeinfo(file_path):
    """加载类型信息JSON文件"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception as e:
        print(f"加载文件失败: {e}")
        sys.exit(1)

def analyze_type_distribution(typeinfo):
    """分析类型分布"""
    type_kind_counter = Counter()
    primitive_counter = Counter()
    literal_counter = Counter()
    file_counter = defaultdict(Counter)

    # 类型字符串到种类的映射
    type_str_to_kind = {
        'string': 'primitive',
        'number': 'primitive',
        'boolean': 'primitive',
        'unknown': 'unknown',
        'string constant': 'literal',
        'number constant': 'literal',
        'boolean constant': 'literal',
        'object constant': 'literal',
        'function': 'function',
        'object': 'object',
        'array': 'array',
    }

    for item in typeinfo:
        if 'type' not in item:
            continue

        type_data = item['type']
        # 处理不同类型的 type 字段：可能是字符串或字典
        if isinstance(type_data, dict):
            kind = type_data.get('kind', 'unknown')
            # 细分统计
            if kind == 'primitive':
                primitive_name = type_data.get('name', 'unknown')
                primitive_counter[primitive_name] += 1
            elif kind == 'literal':
                value = type_data.get('value', 'unknown')
                # 按值类型分类
                if isinstance(value, bool):
                    literal_counter['boolean'] += 1
                elif isinstance(value, (int, float)):
                    literal_counter['number'] += 1
                elif isinstance(value, str):
                    literal_counter['string'] += 1
                else:
                    literal_counter['other'] += 1
        else:
            # type_data 是字符串
            type_str = str(type_data).strip()
            # 默认种类为 unknown
            kind = type_str_to_kind.get(type_str, 'unknown')
            # 对于原始类型，从字符串提取名称
            if kind == 'primitive':
                primitive_counter[type_str] += 1
            elif kind == 'literal':
                # 尝试从 constant 字段获取值
                value = item.get('constant', 'unknown')
                # 按值类型分类
                if isinstance(value, bool):
                    literal_counter['boolean'] += 1
                elif isinstance(value, (int, float)):
                    literal_counter['number'] += 1
                elif isinstance(value, str):
                    literal_counter['string'] += 1
                else:
                    literal_counter['other'] += 1

        type_kind_counter[kind] += 1

        # 按文件统计
        filepath = item.get('relapath', 'unknown')
        file_counter[filepath][kind] += 1

    return {
        'type_kind': dict(type_kind_counter),
        'primitive': dict(primitive_counter),
        'literal': dict(literal_counter),
        'by_file': {f: dict(c) for f, c in file_counter.items()}
    }

def analyze_performance():
    """分析性能数据（如果有的话）"""
    # 这里可以添加性能数据收集逻辑
    # 目前返回空数据
    return {}

def print_statistics(stats):
    """打印统计结果"""
    print("=" * 60)
    print("类型推导结果统计")
    print("=" * 60)

    total_types = sum(stats['type_kind'].values())
    print(f"\n总类型数量: {total_types}")

    print("\n类型种类分布:")
    for kind, count in sorted(stats['type_kind'].items(), key=lambda x: x[1], reverse=True):
        percentage = count / total_types * 100
        print(f"  {kind:15s}: {count:5d} ({percentage:5.1f}%)")

    if stats['primitive']:
        print("\n原始类型细分:")
        primitive_total = sum(stats['primitive'].values())
        for name, count in sorted(stats['primitive'].items(), key=lambda x: x[1], reverse=True):
            percentage = count / primitive_total * 100 if primitive_total > 0 else 0
            print(f"  {name:15s}: {count:5d} ({percentage:5.1f}%)")

    if stats['literal']:
        print("\n字面量类型细分:")
        literal_total = sum(stats['literal'].values())
        for name, count in sorted(stats['literal'].items(), key=lambda x: x[1], reverse=True):
            percentage = count / literal_total * 100 if literal_total > 0 else 0
            print(f"  {name:15s}: {count:5d} ({percentage:5.1f}%)")

    print("\n按文件统计:")
    for filepath, counts in stats['by_file'].items():
        file_total = sum(counts.values())
        print(f"\n  {filepath}: {file_total} 个类型")
        for kind, count in sorted(counts.items(), key=lambda x: x[1], reverse=True):
            if file_total > 0:
                percentage = count / file_total * 100
                print(f"    {kind:15s}: {count:5d} ({percentage:5.1f}%)")

def plot_type_distribution(stats, output_dir='output/stats'):
    """绘制类型分布图表"""
    os.makedirs(output_dir, exist_ok=True)

    # 1. 类型种类分布饼图
    type_kind = stats['type_kind']
    if type_kind:
        plt.figure(figsize=(10, 8))
        labels = list(type_kind.keys())
        sizes = list(type_kind.values())

        # 颜色设置
        colors = plt.cm.Set3(np.linspace(0, 1, len(labels)))

        plt.pie(sizes, labels=labels, autopct='%1.1f%%', startangle=90, colors=colors)
        plt.axis('equal')
        plt.title('Type Category Distribution')
        plt.savefig(os.path.join(output_dir, 'type_kind_pie.png'), dpi=150, bbox_inches='tight')
        plt.close()

    # 2. 原始类型分布条形图
    if stats['primitive']:
        plt.figure(figsize=(10, 6))
        primitive_names = list(stats['primitive'].keys())
        primitive_counts = list(stats['primitive'].values())

        bars = plt.bar(range(len(primitive_names)), primitive_counts, color='skyblue')
        plt.xticks(range(len(primitive_names)), primitive_names, rotation=45, ha='right')
        plt.ylabel('Count')
        plt.title('Primitive Type Distribution')

        # 在柱子上显示数值
        for bar, count in zip(bars, primitive_counts):
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width()/2., height + 0.1,
                    f'{count}', ha='center', va='bottom')

        plt.tight_layout()
        plt.savefig(os.path.join(output_dir, 'primitive_bar.png'), dpi=150, bbox_inches='tight')
        plt.close()

    # 3. 按文件类型数量条形图
    if stats['by_file']:
        plt.figure(figsize=(12, 6))
        files = list(stats['by_file'].keys())
        file_totals = [sum(counts.values()) for counts in stats['by_file'].values()]

        # 取前10个文件（如果有更多）
        if len(files) > 10:
            indices = np.argsort(file_totals)[-10:]
            files = [files[i] for i in indices]
            file_totals = [file_totals[i] for i in indices]

        bars = plt.bar(range(len(files)), file_totals, color='lightgreen')
        plt.xticks(range(len(files)), [os.path.basename(f) for f in files], rotation=45, ha='right')
        plt.ylabel('Type Count')
        plt.title('Type Count per File')

        # 在柱子上显示数值
        for bar, count in zip(bars, file_totals):
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width()/2., height + 0.1,
                    f'{count}', ha='center', va='bottom')

        plt.tight_layout()
        plt.savefig(os.path.join(output_dir, 'file_totals_bar.png'), dpi=150, bbox_inches='tight')
        plt.close()

    # 4. 类型种类堆叠条形图（按文件）
    if stats['by_file']:
        # 获取所有类型种类
        all_kinds = set()
        for counts in stats['by_file'].values():
            all_kinds.update(counts.keys())
        all_kinds = sorted(list(all_kinds))

        # 限制文件数量，避免图表过于拥挤
        max_files = 8
        file_items = list(stats['by_file'].items())
        if len(file_items) > max_files:
            file_items = sorted(file_items, key=lambda x: sum(x[1].values()), reverse=True)[:max_files]

        files = [os.path.basename(f) for f, _ in file_items]

        # 准备堆叠数据
        data = np.zeros((len(files), len(all_kinds)))
        for i, (_, counts) in enumerate(file_items):
            for j, kind in enumerate(all_kinds):
                data[i, j] = counts.get(kind, 0)

        plt.figure(figsize=(12, 8))
        bottom = np.zeros(len(files))
        colors = plt.cm.tab20c(np.linspace(0, 1, len(all_kinds)))

        for j, kind in enumerate(all_kinds):
            plt.bar(files, data[:, j], bottom=bottom, label=kind, color=colors[j])
            bottom += data[:, j]

        plt.ylabel('Type Count')
        plt.title('Type Category Distribution per File (Stacked)')
        plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left')
        plt.xticks(rotation=45, ha='right')
        plt.tight_layout()
        plt.savefig(os.path.join(output_dir, 'file_stacked_bar.png'), dpi=150, bbox_inches='tight')
        plt.close()

    print(f"\n图表已保存到: {output_dir}/")

def main():
    """主函数"""
    # 默认使用 output/typeinfo.json
    typeinfo_path = 'output/typeinfo.json'

    if len(sys.argv) > 1:
        typeinfo_path = sys.argv[1]

    if not os.path.exists(typeinfo_path):
        print(f"错误: 文件不存在: {typeinfo_path}")
        print("请先运行类型推导工具生成 typeinfo.json")
        sys.exit(1)

    print(f"加载文件: {typeinfo_path}")
    typeinfo = load_typeinfo(typeinfo_path)
    print(f"加载完成，共 {len(typeinfo)} 个类型条目")

    # 分析数据
    stats = analyze_type_distribution(typeinfo)

    # 打印统计结果
    print_statistics(stats)

    # 生成图表
    try:
        plot_type_distribution(stats)
        print("\n图表生成成功!")
    except Exception as e:
        print(f"\n图表生成失败: {e}")
        print("请检查 matplotlib 安装或调整代码")

if __name__ == '__main__':
    main()