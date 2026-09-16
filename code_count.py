import os
import sys

def count_lines_in_files(root_dir, target_ext):
    """
    递归统计目录及其子目录中指定后缀的文本文件的总行数。

    参数:
    root_dir: 要遍历统计的根目录
    target_ext: 目标文件后缀（如'.txt'，需包含点号）
    """
    # 确保后缀格式正确
    target_ext = target_ext if target_ext.startswith('.') else '.' + target_ext

    total_files = 0
    total_lines = 0
    error_files = []

    for root, dirs, files in os.walk(root_dir):
        for filename in files:
            # 获取文件扩展名并进行匹配
            name, ext = os.path.splitext(filename)
            if ext.lower() == target_ext.lower():  # 忽略大小写进行比较
                file_path = os.path.join(root, filename)
                total_files += 1
                
                try:
                    # 以文本模式打开文件并统计行数
                    with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                        line_count = sum(1 for _ in f)  # 高效统计行数
                    total_lines += line_count
                    print(f"📄 已统计: {filename} -> {line_count} 行 (位于: {root})")
                except PermissionError as e:
                    print(f"❌ 权限错误，无法读取: {file_path}。错误信息: {e}")
                    error_files.append((file_path, "权限错误"))
                except Exception as e:
                    print(f"❌ 读取失败 {file_path}: {e}")
                    error_files.append((file_path, str(e)))
    
    # 输出总结报告
    print("\n" + "="*50)
    print("统计完成！")
    print(f"📂 目标文件类型: *{target_ext}")
    print(f"📊 统计文件总数: {total_files} 个")
    print(f"📈 累计行数总计: {total_lines} 行")
    if total_files > 0:
        print(f"📐 平均每个文件: {total_lines / total_files:.1f} 行")
    if error_files:
        print(f"⚠️  读取失败: {len(error_files)} 个文件")
        for err_file, reason in error_files[:5]:  # 最多显示5个失败项
            print(f"    - {err_file} : {reason}")
        if len(error_files) > 5:
            print(f"    ... 以及另外 {len(error_files) - 5} 个文件")
    
    return total_files, total_lines

if __name__ == "__main__":
    # 设置默认目录为当前目录
    default_dir = "."
    
    target_directory = input(f"请输入要扫描的根目录路径 (留空则为当前目录 '{os.path.abspath(default_dir)}'): ").strip()
    if not target_directory:
        target_directory = default_dir
    
    # 转换为绝对路径并验证是否存在
    target_directory = os.path.abspath(target_directory)
    if not os.path.isdir(target_directory):
        print(f"错误：指定的目录 '{target_directory}' 不存在！")
        sys.exit(1)
    
    # 获取要统计的文件扩展名
    file_extension = input("请输入要统计的文本文件扩展名 (例如 .txt, .py, .log，留空默认为 .txt): ").strip()
    if not file_extension:
        file_extension = '.txt'
        print(f"将使用默认扩展名: {file_extension}")
    
    print(f"工作目录: {target_directory}")
    print(f"正在递归扫描所有 *{file_extension} 文件并统计行数...\n")
    
    # 执行统计操作
    count_lines_in_files(target_directory, file_extension)
    
    # 针对可能遇到的编码或权限问题给出提示
    print("\n💡 **提示**")
    print("如果脚本报告‘权限错误’或大量文件读取失败，请尝试：")
    print("  1. 确保您对目标目录有读取权限")
    print("  2. 某些非纯文本文件（即使有目标后缀）可能因编码问题导致统计不准确")
    
    # 等待用户按键后再关闭窗口（适用于直接双击运行的情况）
    if sys.stdout.isatty():  # 仅在直接运行时显示此提示
        input("\n按 Enter 键退出...")