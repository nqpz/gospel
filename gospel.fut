import "lib/github.com/diku-dk/lys/lys"
import "lib/github.com/diku-dk/cpprandom/random"
import "lib/github.com/diku-dk/cpprandom/shuffle"

module rnge = minstd_rand
module dist = uniform_int_distribution i32 rnge
module rnge_shuffle = mk_shuffle rnge
type rng = rnge.rng

let size = 19i32

type cell = #white | #black | #empty
type board = [size][size]cell
let empty_board: board = replicate size (replicate size #empty)

type finder_cell = #free | #depending {top: bool, right: bool, bottom: bool, left: bool}
type finder = [size][size]finder_cell

type play_style = #human_vs_human | #human_vs_computer
type computer_strategy = #random_move | #monte_carlo

type point = (i32, i32)

type text_content = (i32, i32, i32, i32, i32, i32, i32)
module lys: lys with text_content = text_content = {
  type state = {board: board, n_turns: i32,
                play_style: play_style, computer_strategy: computer_strategy,
                n_white_stones: i32, n_black_stones: i32,
                h: i32, w: i32, rng: rng, clicked: bool}

  let board_scores (board: board): (i32, i32) =
    -- XXX: This might not follow any of the official rules.
    let (white_stones, black_stones) =
      unzip (map (\cell -> (i32.bool (cell == #white),
                            i32.bool (cell == #black))) (flatten board))
    in (i32.sum white_stones, i32.sum black_stones)

  let player_wins (cell: cell) (board: board): bool =
    let (white_score, black_score) = board_scores board
    in match cell
       case #white -> white_score > black_score
       case #black -> black_score > white_score
       case _ -> false

  let board_index' (s: state) ((yp, xp): point): (f32, f32, f32, i32, i32) =
    let y = r32 yp / r32 s.h
    let x = r32 xp / r32 s.w
    let step = 1 / r32 size
    let yi = t32 (y / step)
    let xi = t32 (x / step)
    in (y, x, step, yi, xi)

  let board_index (s: state) ((yp, xp): point): point =
    let (_y, _x, _step, yi, xi) = board_index' s (yp, xp)
    in (yi, xi)

  let check_liberties (board: board): (board, i32, i32) =
    let other_stone (cell: cell): cell = if cell == #white then #black else #white
    let cell_init (cell: cell) ((y, x): point): finder_cell =
      if cell == #empty
      then #free
      else #depending {top=y > 0 && board[y - 1, x] != other_stone cell,
                       right=x < size - 1 && board[y, x + 1] != other_stone cell,
                       bottom=y < size - 1 && board[y + 1, x] != other_stone cell,
                       left=x > 0 && board[y, x - 1] != other_stone cell}
    let finder_init: finder =
      map2 (\row y -> map2 (\cell x -> cell_init cell (y, x)) row (0..<size))
           board (0..<size)

    let finder_step (finder: finder): (finder, bool) =
      let finder_cell_step (finder_cell: finder_cell) ((y, x): point): (finder_cell, bool) =
        match finder_cell
        case #depending {top, right, bottom, left} ->
          if top && finder[y - 1, x] == #free ||
             right && finder[y, x + 1] == #free ||
             bottom && finder[y + 1, x] == #free ||
             left && finder[y, x - 1] == #free
          then (#free, true)
          else (finder_cell, false)
        case #free -> (#free, false)
      let (finder'_flat, changes) =
        unzip (flatten (map2 (\row y -> map2 (\finder_cell x ->
                                                finder_cell_step finder_cell (y, x)) row (0..<size))
                             finder (0..<size)))
      let finder' = unflatten size size finder'_flat
      let has_change = or changes
      in (finder', has_change)

    let (finder_final, _) = loop (finder, continue) = (finder_init, true)
                            while continue do finder_step finder
    let update_cell (cell: cell) (finder_cell: finder_cell): (cell, i32, i32) =
      match finder_cell
      case #depending _ -> (#empty, i32.bool (cell == #white), i32.bool (cell == #black))
      case #free -> (cell, 0, 0)
    let (board'_flat, removed_white_stones, removed_black_stones) =
      unzip3 (flatten (map2 (map2 update_cell) board finder_final))
    let board' = unflatten size size board'_flat
    in (board', i32.sum removed_white_stones, i32.sum removed_black_stones)

  let check_liberties' (s: state): state =
    let (board', removed_white, removed_black) = check_liberties s.board
    in s with board = board'
         with n_white_stones = s.n_white_stones - removed_white
         with n_black_stones = s.n_black_stones - removed_black

  let current_stone (s: state): cell = if s.n_turns % 2 == 0 then #white else #black

  let next_stone (cell: cell): cell = match cell
                                      case #white -> #black
                                      case #black -> #white
                                      case #empty -> #empty

  let next_turn (s: state): state =
    let current = current_stone s
    in s with n_turns = s.n_turns + 1
         with n_white_stones = s.n_white_stones + i32.bool (current == #white)
         with n_black_stones = s.n_black_stones + i32.bool (current == #black)

  let find_moves (board: board): [](i32, i32) =
    let move_possible cell (y, x) = match cell
                                    case #empty -> (true, (y, x))
                                    case _ -> (false, (-1, -1))
    in (unzip (partition (.0) (flatten (map2 (\row y -> map2 (\cell x -> move_possible cell (y, x))
                                                             row (0..<size)) board (0..<size)))).0).1

  let monte_carlo_iterate (current: cell) (rng: rng) (board: board): (rng, board) =
    let n_iterations = 10i32

    let (_current, rng, board, _i, _continue) =
      loop (current, rng, board, i, continue) = (current, rng, copy board, 1, true)
      while continue
      do let moves_possible = find_moves board
         in if length moves_possible > 0
            then let (rng, move_i) = dist.rand (0, length moves_possible - 1) rng
                 let (y, x) = moves_possible[move_i]
                 let board[y, x] = current
                 let (board, _, _) = check_liberties board
                 in (next_stone current, rng, board, i + 1, i < n_iterations)
            else (current, rng, board, i, false)
    in (rng, board)

  let monte_carlo_score (current: cell) (rng: rng) (board: board): (rng, i32) =
    let n_branches = 10

    let rngs = rnge.split_rng n_branches rng
    let (rngs, branches) = unzip (map2 (monte_carlo_iterate current) rngs (replicate n_branches board))
    let rng = rnge.join_rng rngs
    let n_wins = i32.sum (map (player_wins current >-> i32.bool) branches)
    in (rng, n_wins)

  let monte_carlo [n] (board: board) (moves_possible: [n]point) (current: cell) (rng: rng): (rng, i32) =
    let boards = map (\(y, x) -> copy board with [y, x] = current) moves_possible
    let rngs = rnge.split_rng n rng
    let (rngs, scores) = unzip (map2 (monte_carlo_score (next_stone current)) rngs boards)
    let rng = rnge.join_rng rngs
    let sources = zip (0..<n) scores
    let (rng, sources) = rnge_shuffle.shuffle rng sources
    let (move_i, _score_i) = reduce_comm (\(i1, score1) (i2, score2) -> if score1 > score2
                                                                        then (i1, score1)
                                                                        else (i2, score2))
                                         (-1, -1) sources
    in (rng, move_i)

  let make_computer_move (s: state): state =
    let current = current_stone s
    let moves_possible = find_moves s.board
    in if length moves_possible > 0
       then let (rng, move_i) =
              match s.computer_strategy
              case #random_move -> dist.rand (0, length moves_possible - 1) s.rng
              case #monte_carlo -> monte_carlo s.board moves_possible current s.rng -- XXX: Is silly
            let (move_y, move_x) = moves_possible[move_i]
            let board' = copy s.board
            let board'[move_y, move_x] = current
            let s = s with board = board'
                      with rng = rng
            in check_liberties' (next_turn s)
       else s

  let grab_mouse = false

  let init (seed: u32) (h: i32) (w: i32): state =
    {board=copy empty_board, n_turns=0,
     play_style=#human_vs_computer, computer_strategy=#random_move,
     n_white_stones=0, n_black_stones=0,
     w, h, rng=rnge.rng_from_seed [i32.u32 seed], clicked=false}

  let resize (h: i32) (w: i32) (s: state): state =
    s with h = h with w = w

  let click ((yp, xp): point) (s: state): state =
    let (yi, xi) = board_index s (yp, xp)
    in if s.board[yi, xi] != #empty
       then s
       else let s = let board' = copy s.board
                    let board'[yi, xi] = current_stone s
                    let s = s with board = board'
                    in check_liberties' (next_turn s)
            in match s.play_style
               case #human_vs_human -> s
               case #human_vs_computer -> make_computer_move s

  let event (e: event) (s: state): state =
    let next_play_style (play_style: play_style): play_style =
      match play_style
      case #human_vs_human -> #human_vs_computer
      case #human_vs_computer -> #human_vs_human
    let next_computer_strategy (computer_strategy: computer_strategy): computer_strategy =
      match computer_strategy
      case #random_move -> #monte_carlo
      case #monte_carlo -> #random_move
    in match e
       case #mouse {buttons, x, y} ->
         if buttons == 0b001 && !s.clicked
         then click (y, x) s with clicked = true
         else if buttons == 0
         then s with clicked = false
         else s
       case #keydown {key} ->
         if key == SDLK_1
         then s with play_style = next_play_style s.play_style
         else if key == SDLK_2
         then s with computer_strategy = next_computer_strategy s.computer_strategy
         else s
       case _ -> s

  let render (s: state): [][]argb.colour =
    let render_pixel (yp: i32) (xp: i32): argb.colour =
      let (y, x, step, yi, xi) = board_index' s (yp, xp)
      let y_rel_c = (r32 yi + 0.5) * step
      let x_rel_c = (r32 xi + 0.5) * step
      in if (y - y_rel_c)**2 + (x - x_rel_c)**2 < (step / 2)**2
         then match s.board[yi, xi]
              case #white -> argb.white
              case #black -> argb.black
              case #empty ->
                if yp == t32 (r32 s.h * y_rel_c) ||
                   xp == t32 (r32 s.w * x_rel_c)
                then argb.blue
                else argb.violet
         else argb.violet
    in tabulate_2d s.h s.w render_pixel

  type text_content = text_content

  let text_format () = "             Turn: %d (%[white|black])\n     White stones: %d\n     Black stones: %d\n       Play style: %[Human vs. human|Human vs. computer]\nComputer strategy: %[Random move|Monte carlo] (%[inactive|active])"

  let text_content (_render_duration: f32) (s: state): text_content =
    (s.n_turns, s.n_turns % 2, s.n_white_stones, s.n_black_stones,
     match s.play_style
     case #human_vs_human -> 0
     case #human_vs_computer -> 1,
     match s.computer_strategy
     case #random_move -> 0
     case #monte_carlo -> 1,
     match s.play_style
     case #human_vs_human -> 0
     case #human_vs_computer -> 1)

  let text_colour = const argb.green
}
