#!/usr/bin/env python3

import os
import platform
import subprocess
import sys
import venv


# Determine the executable name based on the platform
stockfish_executable = os.environ.get('STOCKFISH_BIN', 'stockfish')

# Define the path to the script directory and virtual environment directory
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
VENV_DIR = os.path.join(SCRIPT_DIR, 'venv')

def get_venv_python():
    """Get the path to the virtual environment's Python executable."""
    if os.name == 'nt':
        return os.path.join(VENV_DIR, 'Scripts', 'python.exe')
    else:
        # Unix-like
        return os.path.join(VENV_DIR, 'bin', 'python3')

def get_pip_executable():
    """Get the path to the virtual environment's pip executable."""
    if os.name == 'nt':
        return os.path.join(VENV_DIR, 'Scripts', 'pip.exe')
    else:
        return os.path.join(VENV_DIR, 'bin', 'pip3')

def create_virtualenv(venv_path):
    """Creates a virtual environment if it doesn't exist."""
    if not os.path.isdir(venv_path):
        venv.create(venv_path, with_pip=True)

def install_package(venv_path, package):
    """Installs a package in the virtual environment using pip."""
    pip_executable = get_pip_executable()
    # Check if the package is already installed
    try:
        subprocess.check_call([pip_executable, 'show', package], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError:
        # Package is not installed; install it silently
        subprocess.check_call([pip_executable, 'install', package], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def is_running_in_venv():
    """Checks if the script is already running inside the virtual environment."""
    venv_python = get_venv_python()
    return os.path.realpath(sys.executable) == os.path.realpath(venv_python)

def activate_and_run():
    """Runs the chess move logic."""
    # Install python-chess if not installed
    install_package(VENV_DIR, 'python-chess')

    # Now, import chess and the engine after ensuring installation
    import chess
    import chess.engine

    if len(sys.argv) != 2:
        print("Usage: get_next_move.py '<FEN>'")
        sys.exit(1)

    fen = sys.argv[1]
    board = chess.Board(fen)

    # Initialize te engine (specify the path if necessary)
    engine = chess.engine.SimpleEngine.popen_uci(stockfish_executable, timeout=10)

    try:
        # Set a thinking time limit (e.g., 0.1 seconds)
        result = engine.play(board, chess.engine.Limit(time=0.1))
        move = result.move
        # Output the move in Standard Algebraic Notation sans # and +.
        print(board.san(move).replace('+', '').replace('#', ''), flush=True)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    finally:
        if 'NT' in platform.system() or os.name == 'nt':
            os._exit(0)
        else:
            engine.quit()



def run_in_virtualenv():
    """Re-executes the script using the virtual environment's Python."""
    venv_python = get_venv_python()

    # If the current interpreter is not the virtual environment's python, re-execute the script
    if not is_running_in_venv():
        #print("Re-executing the script within the virtual environment...")
        os.execv(venv_python, [venv_python] + sys.argv)

if __name__ == "__main__":
    # Ensure the virtual environment is created
    create_virtualenv(VENV_DIR)

    # Check if we are running inside the virtual environment
    if not is_running_in_venv():
        run_in_virtualenv()
    else:
        activate_and_run()