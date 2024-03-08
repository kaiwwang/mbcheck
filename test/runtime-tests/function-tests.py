import subprocess
import os
import time

# Function to run mbcheck and calculate execution time
def run_mbcheck(file_path):
    execution_times = []  # Store execution times for each run
    output = ""
    parts = file_path.split('/')
    desired_path = '/'.join(parts[:parts.index('mbcheck')+1])
    os.chdir(desired_path)

    # Execute mbcheck 100 times for averaging
    for _ in range(100):
        try:
            start_time = time.time()  # Start timing
            result = subprocess.run(['./mbcheck', file_path], stdout=subprocess.PIPE, text=True)
            end_time = time.time()  # End timing
            execution_times.append(end_time - start_time)  # Append execution time
            output = result.stdout.strip()
        except Exception as e:
            print(f"Execution failed: {e}")
            return "", 0

    # Calculate average execution time
    average_execution_time = sum(execution_times) / len(execution_times)
    return output, average_execution_time

# Function to test all .pat files in the specified directory
def test_directory(directory_path, expected_outputs):
    results = {}
    for filename in os.listdir(directory_path):
        if filename.endswith(".pat"):
            file_path = os.path.join(directory_path, filename)
            output, average_execution_time = run_mbcheck(file_path)
            # If there's an expected output, compare it, otherwise just check if the test ran successfully
            test_passed = (expected_outputs.get(filename, "") == output) if expected_outputs else (output != "")
            results[filename] = (output, average_execution_time, test_passed)
    return results

# Function to print formatted results
def print_results(test_results):
    # Define the column widths
    file_col_width = 20
    output_col_width = 30
    exec_time_col_width = 20
    test_passed_col_width = 10

    # Print the header
    header_format = f"{'File':<{file_col_width}} {'Output':<{output_col_width}} {'Avg Exec Time (ms)':>{exec_time_col_width}} {'Test Passed':>{test_passed_col_width}}"
    print(header_format)
    print("-" * len(header_format))

    # Print the formatted results
    for file, (output, average_execution_time, test_passed) in sorted(test_results.items()):
        # Handle long outputs with newlines
        output_lines = [output[i:i+output_col_width] for i in range(0, len(output), output_col_width)]
        first_line_output = output_lines.pop(0) if output_lines else output
        passed_text = "Passed" if test_passed else "Failed"
        print(f"{file:<{file_col_width}} {first_line_output:<{output_col_width}} {average_execution_time*1000:>{exec_time_col_width}.3f} {passed_text:>{test_passed_col_width}}")
        for additional_line in output_lines:
            print(f"{'':<{file_col_width}} {additional_line:<{output_col_width}}")

# Main function
if __name__ == "__main__":
    current_path = os.path.abspath(__file__)
    father_path = os.path.abspath(os.path.dirname(current_path) + os.path.sep + ".")
    base_directory = os.path.abspath(os.path.dirname(current_path) + os.path.sep + "..")

    # Expected outputs for each directory
    expected_outputs = {
        "examples/de_liguoro_padovani": {
            "sessions.pat": "6",
            "master_worker.pat": "55385",
            "lock.pat": "12",
            "future.pat": "55",
            "account_future.pat": "INFO: Terminating account.INFO: Terminating account.",
            "futurefail.pat": "55",
            "account.pat": ""
        },
        "examples/savina": {
            "ping_pong.pat": "",
            "philosopher.pat": "",
            "count.pat": "Total: 5",
            "thread_ring.pat": "",
            "banking.pat": "",
            "fib_pairs.pat": "",
            "cig_smok.pat": "",
            "log_map.pat": "",
            "big.pat": "",
            "fib.pat": "Result: 5",
            "ping_pong_strict.pat": "",
            "kfork.pat": ""
        },   
        "pat-tests": {
            "arith2.pat": "",
            "arith1.pat": "",
            "linfun-bad-3.pat": "",
            "linfun-bad-2.pat": "",
            "linfun-bad-1.pat": "",
            "functions.pat": "",
            "sum-1.pat": "5",
            "sum-2.pat": "5",
            "linfun-good.pat": "",
            "let-annot-2.pat": "",
            "arith.pat": "",
            "let-annot-3.pat": "",
            "let-annot-1.pat": ""
    }
        
    }

    # Test results for both directories
    for dir_name, dir_expected_outputs in expected_outputs.items():
        print(f"\nTesting directory: {dir_name}\n")
        directory_path = os.path.join(base_directory, dir_name)
        test_results = test_directory(directory_path, dir_expected_outputs)
        print_results(test_results)
