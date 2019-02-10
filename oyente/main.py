import subprocess
import os
import re
import json
import threading
import time


def test_trace(root_dir, trace, code):
    """

    :param root_dir:
    :param trace:
    :param code:
    :return:
    """
    trace_path = os.path.join(root_dir, trace)
    code_path = os.path.join(root_dir, code)

    cmd = subprocess.Popen('python oyente.py -s {} -tf {} -b'.format(code_path, trace_path),
                           shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = cmd.communicate()

    if not cmd.returncode == 0:  # an error occurred
        return {'trace': trace, 'code': code, 'succeed': False, 'info': 'Runtime error', 'stdout': stdout,
                'stderr': stderr}
    else:
        path_condition_and_vars_sep = '============ Path Conditions and Variables ==========='
        path_condition_sep = '============ Path Condition ==========='
        variables_sep = '============ Variables ==========='
        var_origins_sep = '============ Variable Origins ==========='

        lines = [line.strip() for line in stdout.split('\n') if not line.strip() == '']
        path_condition_and_vars_index = path_condition_index = variables_index = var_origins_index = 0
        for i, line in enumerate(lines):
            if line == path_condition_and_vars_sep:
                path_condition_and_vars_index = i
            elif line == path_condition_sep:
                path_condition_index = i
            elif line == variables_sep:
                variables_index = i
            elif line == var_origins_sep:
                var_origins_index = i

        return {'trace': trace, 'code': code, 'succeed': True, 'info': 'OK',
                'path_condition_and_vars': '\n'.join(lines[path_condition_and_vars_index + 1: path_condition_index]),
                'path_condition': '\n'.join(lines[path_condition_index + 1: variables_index]),
                'variables': '\n'.join(lines[variables_index + 1: var_origins_index]),
                'var_origins': '\n'.join(lines[var_origins_index + 1:])}


def on_test_traces(index, test_traces, result_dir):
    """

    :param index:
    :param test_traces:
    :param result_dir:
    :return:
    """
    trace_doc_pattern = re.compile(r'^trace_doc_((\d+)_(\d+))$')
    trace_code_pattern = re.compile(r'^code_((\d+)_(\d+))$')
    evm_pattern = re.compile(r'^.+\.evm$')
    evm_disasm_pattern = re.compile(r'^.+\.evm\.disasm$')

    root_dir = os.path.join(test_traces, str(index))
    file_list = [file for file in os.listdir(root_dir)
                 if not evm_pattern.match(file) and not evm_disasm_pattern.match(file)]
    trace_list = [file for file in file_list if trace_doc_pattern.match(file)]  # trace file names
    code_list = [file for file in file_list if trace_code_pattern.match(file)]  # code file names

    sorted_trace_list = sorted(trace_list, key=lambda trace: int(trace_doc_pattern.match(trace).group(3)))
    sorted_code_list = sorted(code_list, key=lambda code: int(trace_code_pattern.match(code).group(3)))

    write_lock = threading.Lock()
    result_file = open(os.path.join(result_dir, str(index)), 'w')

    def simple_job(root_dir, trace, code, write_lock, result_file):  # simple thread job
        """

        :param root_dir:
        :param trace:
        :param code:
        :param write_lock:
        :return:
        """
        test_result = test_trace(root_dir, trace, code)
        write_lock.acquire()
        result_file.write(json.dumps(test_result) + '\n')
        write_lock.release()
        print trace

    for trace in sorted_trace_list:
        if threading.active_count() <= 11:  # we accept maximal 10 job threads concurrently
            code = 'code_{}'.format(trace_doc_pattern.match(trace).group(1))
            if code not in sorted_code_list:  # no code found (probably due to bad JSON-RPC request)
                test_result = {'trace': trace, 'succeed': False, 'info': 'No code file exists'}
                result_file.write(json.dumps(test_result) + '\n')
            else:
                threading.Thread(target=simple_job, args=(root_dir, trace, code, write_lock, result_file)).start()
                # test_result = test_trace(root_dir, trace, code)
                # result_file.write(json.dumps(test_result) + '\n')
        else:
            time.sleep(1)

    while threading.active_count() > 1:  # wait if there are active jobs
        time.sleep(1)  # sleep 1 second

    result_file.close()


def show_results(index, result_dir, seq_num, num_cases=1, only_exception=False):
    """

    :param index:
    :param result_dir:
    :param seq_num:
    :param num_cases: show multiple instances at one time
    :param only_exception: only show exceptional results
    :return:
    """
    trace_doc_pattern = re.compile(r'^trace_doc_((\d+)_(\d+))$')

    with open(os.path.join(result_dir, str(index))) as f:
        result_list = [json.loads(line) for line in f]
    result_list = sorted(result_list, key=lambda r: int(trace_doc_pattern.match(r['trace']).group(3)))
    result_list = [result for result in result_list
                   if int(trace_doc_pattern.match(result['trace']).group(3)) >= seq_num]
    if only_exception:
        result_list = [result for result in result_list if not result['succeed']]

    show_more = True
    current_pos = 0
    while show_more:
        for i in range(num_cases):
            if current_pos + i >= len(result_list):
                show_more = False
                break
            else:
                print '{sep} {num}: {trace} {sep}\n'.format(sep='=' * 10, num=current_pos + i,
                                                           trace=result_list[current_pos + i]['trace'])
                if result_list[current_pos + i]['succeed']:
                    print '{sep} Path Condition {sep}\n'.format(sep='=' * 10)
                    print result_list[current_pos + i]['path_condition']
                    print '{sep} Variable Origins {sep}\n'.format(sep='=' * 10)
                    print result_list[current_pos + i]['var_origins']
                else:
                    print '{sep} Error: StdErr {sep}\n'.format(sep='=' * 10)
                    print result_list[current_pos + i]['stderr']
                    print '{sep} Error: StdOut {sep}\n'.format(sep='=' * 10)
                    print result_list[current_pos + i]['stdout']

        if not show_more:
            print '{sep} The End {sep}'.format(sep='=' * 10)
            break

        current_pos += num_cases
        try:
            if raw_input('Continue? [y]/n: ') == 'n':
                show_more = False
        except SyntaxError:
            pass


if __name__ == '__main__':
    # on_test_traces(0, 'test_traces', 'result')
    # on_test_traces(1, 'test_traces', 'result')
    # on_test_traces(2, 'test_traces', 'result')
    # on_test_traces(3, 'test_traces', 'result')
    # on_test_traces(4, 'test_traces', 'result')
    # on_test_traces(5, 'test_traces', 'result')
    # on_test_traces(6, 'test_traces', 'result')
    # on_test_traces(7, 'test_traces', 'result')
    # on_test_traces(8, 'test_traces', 'result')
    # on_test_traces(9, 'test_traces', 'result')

    # show_results(0, 'result', 151, num_cases=1, only_exception=False)
    # show_results(1, 'result', 0, num_cases=1, only_exception=True)
    show_results(2, 'result', 0, num_cases=1, only_exception=True)
