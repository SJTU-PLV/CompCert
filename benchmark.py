import os
import glob
import subprocess
import time
import csv
import sys
import shutil

# ================= 配置区域 =================
# 自动探测 ccomp 位置
POSSIBLE_CCOMP = ["./ccomp", "./CompCert-c2rust-light/ccomp", "../ccomp"]
# 自动探测 test/c 位置
POSSIBLE_TEST_DIR = ["test/c", "CompCert-c2rust-light/test/c", "../test/c"]

# 结果保存文件
RESULTS_FILE = "benchmark_results.csv" 
# 临时运行目录 (所有生成的垃圾文件都放这里)
TEMP_RUN_DIR = "test/test_run"

TIMEOUT_SEC = 10.0            

# 编译器命令
GCC_CMD = "gcc" 
GCC_FLAGS = ["-O2", "-Wno-return-type", "-Wno-implicit-int"] 

RUSTC_CMD = "rustc"
# 忽略警告，链接 runtime
RUST_FLAGS = ["-O", "--cap-lints=allow"] 

# 自动寻找 runtime
POSSIBLE_RUNTIME = ["runtime", "CompCert-c2rust-light/runtime", "../runtime"]

def find_path(candidates, target_name):
    for p in candidates:
        if os.path.exists(p):
            return p
    return None

def clean_file(filepath):
    """安全删除文件"""
    if filepath and os.path.exists(filepath):
        try:
            os.remove(filepath)
        except OSError:
            pass

def run_command(command, timeout=None, capture_output=True, text=True):
    start_time = time.time()
    try:
        result = subprocess.run(
            command,
            capture_output=capture_output,
            text=text,
            timeout=timeout
        )
        duration = time.time() - start_time
        if result.returncode != 0:
            return False, result.stdout, result.stderr, duration
        return True, result.stdout, result.stderr, duration
    except subprocess.TimeoutExpired:
        empty = "" if text else b""
        timeout_msg = "TIMEOUT" if text else b"TIMEOUT"
        return False, empty, timeout_msg, timeout
    except Exception as e:
        empty = "" if text else b""
        err_msg = str(e) if text else str(e).encode("utf-8", errors="replace")
        return False, empty, err_msg, 0

def outputs_equal(c_out, rs_out):
    """Compare stdout from C/Rust runs.

    - If both outputs are valid UTF-8, compare as stripped text (keeps old behavior).
    - Otherwise compare raw bytes (for binary outputs like PBM).
    """
    def normalize(out):
        if isinstance(out, bytes):
            try:
                return out.decode("utf-8").strip()
            except UnicodeDecodeError:
                return out
        return out.strip()

    return normalize(c_out) == normalize(rs_out)

def benchmark_single_file(c_file_path, ccomp_bin, runtime_path, temp_dir):
    base_name = os.path.splitext(os.path.basename(c_file_path))[0]
    
    # === 定义所有临时文件的路径 (全部在 temp_dir 下) ===
    exe_c = os.path.join(temp_dir, f"{base_name}_c")
    exe_rs = os.path.join(temp_dir, f"{base_name}_rs")
    
    # 最终期望的 rust 文件位置
    rs_file_target = os.path.join(temp_dir, f"{base_name}.rs")
    
    # 初始生成的 rust 文件位置 (ccomp 通常生成在当前工作目录)
    rs_file_generated_cwd = f"{base_name}.rs" 

    result_data = {
        "Benchmark": base_name,
        "Status": "OK",
        "C_Time": 0.0,
        "Rust_Time": 0.0,
        "Overhead": 0.0,
        "Note": ""
    }

    print(f"Testing {base_name:<15} ...", end=" ", flush=True)

    # --- 1. GCC 编译 (输出到 temp_dir) ---
    compile_cmd = [GCC_CMD] + GCC_FLAGS + [c_file_path, "-o", exe_c]
    success, _, stderr, _ = run_command(compile_cmd)
    if not success:
        result_data["Status"] = "C_FAIL"
        result_data["Note"] = "GCC Compile Fail"
        print("❌ C Compile Fail")
        return result_data

    # --- 2. 运行 C 程序 ---
    success, c_out, _, c_time = run_command([exe_c], timeout=TIMEOUT_SEC, text=False)
    clean_file(exe_c) # 跑完就删，保持整洁
    if not success:
        result_data["Status"] = "C_ERR"
        result_data["Note"] = "Runtime Error"
        print("❌ C Runtime Error")
        return result_data
    
    result_data["C_Time"] = round(c_time, 4)

    # --- 3. C -> Rust 翻译 ---
    # ccomp 会在当前目录生成 .rs 文件
    trans_cmd = [ccomp_bin, "-drustlight", c_file_path]
    success, _, stderr, _ = run_command(trans_cmd)
    
    # 移动生成的 .rs 文件到 temp_dir
    moved = False
    if os.path.exists(rs_file_generated_cwd):
        shutil.move(rs_file_generated_cwd, rs_file_target)
        moved = True
    elif os.path.exists(rs_file_target):
        # 极少数情况下如果 ccomp 支持输出路径
        moved = True
    
    # 有些情况下，ccomp 可能在后端报错并返回非 0，但 Rust 文件已成功生成。
    # 只要 .rs 成功生成并移动，就认为“翻译成功”，后续交给 rustc/runtime 再验证。
    if not moved:
        result_data["Status"] = "TRANS_FAIL"
        err_msg = stderr.strip().split('\n')[0][:30] if stderr else "Generation failed"
        result_data["Note"] = err_msg
        print(f"❌ Translation Fail")
        # 清理残留
        clean_file(rs_file_generated_cwd) 
        return result_data

    # --- 4. Rust 编译 (在 temp_dir 中进行) ---
    rust_flags = RUST_FLAGS + ["-L", runtime_path]
    rust_compile_cmd = [RUSTC_CMD] + rust_flags + [rs_file_target, "-o", exe_rs]
    success, _, stderr, _ = run_command(rust_compile_cmd)
    if not success:
        result_data["Status"] = "RS_BUILD_FAIL"
        err_lines = [l for l in stderr.split('\n') if "error[" in l or "error:" in l]
        result_data["Note"] = err_lines[0][:50] if err_lines else "Compile Error"
        print("❌ Rust Compile Fail")
        # 编译失败时，保留 .rs 文件以便调试，不删除
        return result_data

    # --- 5. 运行 Rust 程序 ---
    success, rs_out, _, rs_time = run_command([exe_rs], timeout=TIMEOUT_SEC, text=False)
    
    # 运行成功后清理文件
    clean_file(exe_rs)
    clean_file(rs_file_target) 

    if not success:
        result_data["Status"] = "RS_RUN_FAIL"
        result_data["Note"] = "Panic/Timeout"
        print("❌ Rust Runtime Error")
        return result_data

    result_data["Rust_Time"] = round(rs_time, 4)

    # --- 6. 结果验证 ---
    if not outputs_equal(c_out, rs_out):
        result_data["Status"] = "MISMATCH"
        print(f"⚠️  Output Mismatch")
    else:
        overhead = 0.0
        if c_time > 0.0001:
            overhead = rs_time / c_time
        result_data["Overhead"] = round(overhead, 2)
        print(f"✅ Pass (x{overhead:.2f})")

    return result_data

def main():
    print("=== Clight2Rustlight Benchmark Script (Isolated Run) ===")
    
    # 1. 环境检查
    ccomp_bin = find_path(POSSIBLE_CCOMP, "ccomp")
    if not ccomp_bin:
        print("Error: Could not find 'ccomp'. Run 'make' first.")
        sys.exit(1)

    test_dir = find_path(POSSIBLE_TEST_DIR, "test/c")
    if not test_dir:
        print("Error: Could not find 'test/c'.")
        sys.exit(1)

    runtime_dir = find_path(POSSIBLE_RUNTIME, "runtime")
    if not runtime_dir:
        print("Warning: Could not find 'runtime'.")
        runtime_dir = "." # fallback

    # 2. 创建临时目录
    if not os.path.exists(TEMP_RUN_DIR):
        try:
            os.makedirs(TEMP_RUN_DIR)
            print(f"[*] Created temp directory: {TEMP_RUN_DIR}")
        except OSError as e:
            print(f"Error creating directory {TEMP_RUN_DIR}: {e}")
            sys.exit(1)
    else:
        print(f"[*] Using temp directory: {TEMP_RUN_DIR}")

    # 3. 扫描文件
    c_files = sorted(glob.glob(os.path.join(test_dir, "*.c")))
    if not c_files:
        print(f"Error: No .c files found in {test_dir}")
        sys.exit(1)
    
    print(f"[*] Found {len(c_files)} benchmarks.")
    print(f"[*] Results will be saved to: {RESULTS_FILE}")
    print("-" * 65)

    # 4. 执行
    results = []
    for c_file in c_files:
        res = benchmark_single_file(c_file, ccomp_bin, runtime_dir, TEMP_RUN_DIR)
        results.append(res)

    # 5. 保存结果
    fieldnames = ["Benchmark", "Status", "C_Time", "Rust_Time", "Overhead", "Note"]
    try:
        with open(RESULTS_FILE, mode='w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            for row in results:
                writer.writerow(row)
        print("-" * 65)
        print(f"Done! Check {RESULTS_FILE} for details.")
    except Exception as e:
        print(f"Error saving csv: {e}")

if __name__ == "__main__":
    main()
