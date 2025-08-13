import re
import os

def transform_when_blocks(input_file_path):
    with open(input_file_path, 'r') as input_file:
        lines = input_file.readlines()

    transformed_lines = []
    indent_stack = []

    for line in lines:
        # print(line)
        stripped_line = line.lstrip()
        
        # Calculate current indent
        current_indent = len(line) - len(stripped_line)
        # print(current_indent)
        # print(indent_stack)

        for ids in indent_stack[::-1]:
          if ids >= current_indent:
            transformed_lines.append(' ' * current_indent + '}\n')
            indent_stack.remove(ids)
        # print(indent_stack)
        transformed_lines.append(line)

        # If we see a 'when'
        if stripped_line.startswith("when ") or stripped_line.startswith("else:") or stripped_line.startswith("else :"):

            # Open a new block
            transformed_lines.append(' ' * current_indent + '{\n')
            indent_stack.append(current_indent)
        # print(indent_stack)
    # Close any remaining blocks
    while indent_stack:
        transformed_lines.append(' ' * indent_stack.pop() + '}\n')

    folder_name = "preprowhen"

    # 检查并创建文件夹（如果不存在）
    if not os.path.exists(folder_name):
        os.makedirs(folder_name)
        print(f"已创建文件夹: {folder_name}")
    else:
        print(f"文件夹已存在: {folder_name}")

    # Generating output file path with 'pre' prefix
    dir_name, base_name = os.path.split(input_file_path)
    new_base_name = 'preprowhen/' + base_name
    output_file_path = os.path.join("./", new_base_name)

    # Write the transformed lines to the output file
    with open(output_file_path, 'w') as output_file:
        output_file.writelines(transformed_lines)

    return output_file_path

# Example usage:
if __name__ == '__main__':
    import sys
    if len(sys.argv) != 2:
        print("Usage: python transform_when_blocks.py input_file")
        sys.exit(1)
    
    # Getting the new file path
    new_file_path = transform_when_blocks(sys.argv[1])
    print(f"Transformed file is saved as: {new_file_path}")