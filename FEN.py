UNICODE_PIECE = {
    'r': '♜', 'n': '♞', 'b': '♝', 'q': '♛', 'k': '♚', 'p': '♟',
    'R': '♖', 'N': '♘', 'B': '♗', 'Q': '♕', 'K': '♔', 'P': '♙',
}

def square_color(rank, file):
    # rank, file are 0-based; rank 0 = 8th rank
    return "░░" if (rank + file) % 2 == 0 else "▓▓"

def render_fen(fen: str) -> str:
    board_part, turn, *_ = fen.split()
    ranks = board_part.split("/")

    lines = []
    lines.append("      ╔════════════════╗")

    for r, rank_str in enumerate(ranks):
        row = ""
        file = 0
        for ch in rank_str:
            if ch.isdigit():
                for _ in range(int(ch)):
                    row += square_color(r, file)
                    file += 1
            else:
                piece = UNICODE_PIECE[ch]
                if ch.lower() == 'k' and ((turn == 'w' and ch.isupper()) or
                                          (turn == 'b' and ch.islower())):
                    row += piece + "}"
                else:
                    row += piece + "]"
                file += 1

        assert file == 8, "Rank does not have 8 squares"
        lines.append(f"      ║{row}║")

    lines.append("      ╚════════════════╝")
    return "\n".join(lines)

fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
print(render_fen(fen))

fen = "Bq1B1K2/3PpN2/P3Pp2/P1p2P2/2Pk1b1R/1p6/pN1P1P2/QR6 w KQkq - 0 1"
print(render_fen(fen))