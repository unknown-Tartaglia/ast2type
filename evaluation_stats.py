#!/usr/bin/env python3
"""
类型推导准确率统计脚本
分析 evaluation.json 文件，生成准确率统计图表
"""

import json
import os
import sys
import matplotlib.pyplot as plt
import numpy as np

def load_evaluation(file_path):
    """加载评估结果JSON文件"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception as e:
        print(f"加载文件失败: {e}")
        sys.exit(1)

def analyze_accuracy(evaluation):
    """分析准确率数据"""
    # 主要统计字段
    total = evaluation.get('total', 0)
    correct = evaluation.get('correct', 0)
    wrong = evaluation.get('wrong', 0)
    missing = evaluation.get('missing', 0)
    any_type = evaluation.get('any', 0)  # any类型推导
    unknown = evaluation.get('unknown', 0)

    # 计算其他统计
    other = total - (correct + wrong + missing + any_type + unknown)
    other = max(0, other)  # 确保非负

    # 计算准确率
    accuracy_rate = correct / total * 100 if total > 0 else 0
    coverage_rate = (correct + wrong + any_type) / total * 100 if total > 0 else 0

    # 计算错误类型分布
    error_total = wrong + missing + unknown + other
    wrong_rate = wrong / error_total * 100 if error_total > 0 else 0
    missing_rate = missing / error_total * 100 if error_total > 0 else 0
    unknown_rate = unknown / error_total * 100 if error_total > 0 else 0
    other_rate = other / error_total * 100 if error_total > 0 else 0

    return {
        'total': total,
        'correct': correct,
        'wrong': wrong,
        'missing': missing,
        'any': any_type,
        'unknown': unknown,
        'other': other,
        'accuracy_rate': accuracy_rate,
        'coverage_rate': coverage_rate,
        'error_total': error_total,
        'wrong_rate': wrong_rate,
        'missing_rate': missing_rate,
        'unknown_rate': unknown_rate,
        'other_rate': other_rate,
    }

def print_accuracy_statistics(stats):
    """打印准确率统计结果"""
    print("=" * 60)
    print("类型推导准确率统计")
    print("=" * 60)

    print(f"\n总体统计:")
    print(f"  总类型数量: {stats['total']}")
    print(f"  正确推导: {stats['correct']} ({stats['accuracy_rate']:.1f}%)")
    print(f"  推导覆盖率: {stats['coverage_rate']:.1f}% (正确+错误+any)")

    print(f"\n详细分布:")
    print(f"  Correct (正确): {stats['correct']:6d}")
    print(f"  Wrong (错误推导): {stats['wrong']:6d}")
    print(f"  Missing (缺失推导): {stats['missing']:6d}")
    print(f"  Any (推导为any): {stats['any']:6d}")
    print(f"  Unknown (未知类型): {stats['unknown']:6d}")
    print(f"  Other (其他): {stats['other']:6d}")

    if stats['error_total'] > 0:
        print(f"\n错误类型分布 (共 {stats['error_total']} 个错误):")
        print(f"  Wrong: {stats['wrong_rate']:.1f}%")
        print(f"  Missing: {stats['missing_rate']:.1f}%")
        print(f"  Unknown: {stats['unknown_rate']:.1f}%")
        print(f"  Other: {stats['other_rate']:.1f}%")

def plot_accuracy_charts(stats, output_dir='output/stats'):
    """绘制准确率统计图表"""
    os.makedirs(output_dir, exist_ok=True)

    # 1. 总体分布饼图
    labels = ['Correct', 'Wrong', 'Missing', 'Any', 'Unknown', 'Other']
    sizes = [stats['correct'], stats['wrong'], stats['missing'],
             stats['any'], stats['unknown'], stats['other']]

    # 移除零值的项目
    valid_indices = [i for i, size in enumerate(sizes) if size > 0]
    labels = [labels[i] for i in valid_indices]
    sizes = [sizes[i] for i in valid_indices]

    if sizes:
        plt.figure(figsize=(10, 8))
        colors = ['#4CAF50', '#F44336', '#FF9800', '#2196F3', '#9C27B0', '#795548']
        valid_colors = [colors[i] for i in valid_indices]

        plt.pie(sizes, labels=labels, autopct='%1.1f%%', startangle=90,
                colors=valid_colors, textprops={'fontsize': 12})
        plt.axis('equal')
        plt.title(f'Type Inference Accuracy Distribution\nTotal: {stats["total"]} types, Accuracy: {stats["accuracy_rate"]:.1f}%',
                 fontsize=14, fontweight='bold')
        plt.savefig(os.path.join(output_dir, 'accuracy_distribution.png'), dpi=150, bbox_inches='tight')
        plt.close()

    # 2. 错误类型分布饼图 (仅当有错误时)
    if stats['error_total'] > 0:
        error_labels = ['Wrong', 'Missing', 'Unknown', 'Other']
        error_sizes = [stats['wrong'], stats['missing'], stats['unknown'], stats['other']]

        # 移除零值
        error_valid_indices = [i for i, size in enumerate(error_sizes) if size > 0]
        error_labels = [error_labels[i] for i in error_valid_indices]
        error_sizes = [error_sizes[i] for i in error_valid_indices]

        if error_sizes:
            plt.figure(figsize=(10, 8))
            error_colors = ['#F44336', '#FF9800', '#9C27B0', '#795548']
            valid_error_colors = [error_colors[i] for i in error_valid_indices]

            plt.pie(error_sizes, labels=error_labels, autopct='%1.1f%%', startangle=90,
                    colors=valid_error_colors, textprops={'fontsize': 12})
            plt.axis('equal')
            plt.title(f'Error Type Distribution\nTotal Errors: {stats["error_total"]}',
                     fontsize=14, fontweight='bold')
            plt.savefig(os.path.join(output_dir, 'error_distribution.png'), dpi=150, bbox_inches='tight')
            plt.close()

    # 3. 准确率对比条形图
    plt.figure(figsize=(12, 6))
    metrics = ['Correct', 'Wrong', 'Missing', 'Any', 'Unknown']
    values = [stats['correct'], stats['wrong'], stats['missing'], stats['any'], stats['unknown']]
    colors = ['#4CAF50', '#F44336', '#FF9800', '#2196F3', '#9C27B0']

    bars = plt.bar(range(len(metrics)), values, color=colors)
    plt.xticks(range(len(metrics)), metrics, fontsize=12)
    plt.ylabel('Count', fontsize=12)
    plt.title('Type Inference Metrics Comparison', fontsize=14, fontweight='bold')
    plt.grid(axis='y', alpha=0.3)

    # 在柱子上显示数值
    for bar, value in zip(bars, values):
        height = bar.get_height()
        plt.text(bar.get_x() + bar.get_width()/2., height + 0.5,
                f'{value}', ha='center', va='bottom', fontsize=11)

    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, 'accuracy_comparison.png'), dpi=150, bbox_inches='tight')
    plt.close()

    print(f"\n准确率图表已保存到: {output_dir}/")

def main():
    """主函数"""
    # 默认使用 output/evaluation.json
    evaluation_path = 'output/evaluation.json'

    if len(sys.argv) > 1:
        evaluation_path = sys.argv[1]

    if not os.path.exists(evaluation_path):
        print(f"错误: 文件不存在: {evaluation_path}")
        print("请先运行类型推导工具生成 evaluation.json")
        sys.exit(1)

    print(f"加载文件: {evaluation_path}")
    evaluation = load_evaluation(evaluation_path)

    # 分析数据
    stats = analyze_accuracy(evaluation)

    # 打印统计结果
    print_accuracy_statistics(stats)

    # 生成图表
    try:
        plot_accuracy_charts(stats)
        print("\n准确率图表生成成功!")
    except Exception as e:
        print(f"\n图表生成失败: {e}")
        import traceback
        traceback.print_exc()
        print("请检查 matplotlib 安装或调整代码")

if __name__ == '__main__':
    main()