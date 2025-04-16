import curses
import time
import random
import os
import collections
import argparse
import sys
import traceback
import math # For size calculations, ceil

# --- Constants --- (Unchanged from v2.7)

# Game Element Symbols
FOOD_SYMBOL = '#'; SNAKE_SYMBOL = '*'; WALL_SYMBOL = '%'
OBSTACLE_SYMBOL = '@'; ENEMY_SNAKE_SYMBOL = 'X'; METEOR_SYMBOL = '*'
BALL_SYMBOL = 'o'; THICK_SNAKE_EXTRA_SYMBOL = '+'; UNIFIED_POWERUP_SYMBOL = '?'

# Powerup Types and Names
POWERUP_NAMES = {
    1: "Multi-Food & Slowdown", 2: "Bouncing Balls", 3: "Thick Snake", 4: "MAX SPEED",
    5: "Enemy Snake", 6: "Obstacle Blocks", 7: "Meteor Rain", 8: "Wide Maze"
}
POWERUP_TYPES = list(POWERUP_NAMES.keys())
POWERUP_SYMBOLS = {ptype: UNIFIED_POWERUP_SYMBOL for ptype in POWERUP_TYPES}

# Speed & Timing Configuration
MIN_TIMEOUT = 25; MAX_TIMEOUT = 300; FLASH_INTERVAL = 0.15
TYPE1_DECREMENT_INTERVAL = 180; FLASH_MESSAGE_DURATION = 2.0
MAZE_INITIAL_FREEZE_S = 3; MAZE_SLOWDOWN_FACTOR = 3.0
MAZE_AREA_PERCENTAGE = 0.20; MAZE_CORRIDOR_WIDTH = 3; MAZE_FOOD_DENSITY = 4
ENEMY_SPLIT_SLOWDOWN = 0.25
ENEMY_MOVE_DELAY_BASE = 1
ENEMY_MOVE_DELAY_SPLIT = math.ceil(ENEMY_MOVE_DELAY_BASE / (1.0 - ENEMY_SPLIT_SLOWDOWN))

# High Score Config
HIGHSCORE_FILE = "snake_highscore.txt"; MAX_HIGH_SCORES = 5; MAX_NAME_LENGTH = 10

# Color Pair IDs
DEFAULT_PAIR = 1; FOOD_PAIR = 2; POWERUP_TYPE_1_PAIR = 3; POWERUP_TYPE_2_PAIR = 4
POWERUP_TYPE_3_PAIR = 5; POWERUP_TYPE_4_PAIR = 6; POWERUP_TYPE_5_PAIR = 7
OBSTACLE_PAIR = 11; POWERUP_TYPE_6_PAIR = OBSTACLE_PAIR
METEOR_PAIR = 12; POWERUP_TYPE_7_PAIR = METEOR_PAIR
MAZE_FOOD_PAIR = 14; POWERUP_TYPE_8_PAIR = MAZE_FOOD_PAIR
SNAKE_FLASH_PAIR = 8; ENEMY_SNAKE_PAIR = 9; BALL_PAIR = 10
MAZE_WALL_PAIR = 13; MAZE_SNAKE_PAIR = 16

# Difficulty Levels
DIFFICULTY_LEVELS = {
    "1": {"name": "Easy", "timeout": 150, "increase": 2, "slowdown": 60},
    "2": {"name": "Medium", "timeout": 100, "increase": 4, "slowdown": 45},
    "3": {"name": "Hard", "timeout": 70, "increase": 7, "slowdown": 30},
}

# Power-up Durations
POWERUP_DURATIONS = {
    1: lambda: random.uniform(20, 40), 2: lambda: 8, 3: lambda: 10, 4: lambda: 5,
    5: lambda: 30, 6: lambda: 60, 7: lambda: 7,
    8: {"1": 30, "2": 45, "3": 60}
}
TIMED_EFFECTS_TO_DISPLAY = {1, 2, 3, 4, 5, 7, 8}

# Power-up Specific Consts
BALL_MAX_SPEED = 1; ENEMY_RANDOM_MOVE_CHANCE = 0.15
MAX_OBSTACLE_PLACEMENT_ATTEMPTS = 100

# Score Constants
SCORE_FOOD = 10; SCORE_MAZE_FOOD = 15; SCORE_POWERUP = 25
PENALTY_BALL = -5; PENALTY_METEOR = -2; PENALTY_OBSTACLE_FAIL = -15

# --- Global State Variables --- (Unchanged)
active_effects = []; last_flash_time = 0; flash_on = False; ball_powerup_count = 0
type1_food_spawn_count = 0; last_type1_decrement_time = 0
key_press_history = collections.deque(maxlen=3); maze_food_items = []; foods = []
power_ups_on_screen = []; score = 0; flash_message = None; flash_message_end_time = 0
maze_just_activated = False
speed_increase_factor = 0.0

# --- Custom Exception ---
class TerminalTooSmallError(Exception):
    """Custom exception for when the terminal window is too small."""
    pass

# --- High Score Functions --- (Unchanged)
def load_high_scores():
    scores_list = []
    if not os.path.exists(HIGHSCORE_FILE): return []
    try:
        with open(HIGHSCORE_FILE, "r") as f:
            for line in f:
                line = line.strip();
                if not line: continue
                parts = line.split(',', 1)
                if len(parts) == 2 and parts[0].isdigit():
                    loaded_score = int(parts[0])
                    name = parts[1][:MAX_NAME_LENGTH]
                    scores_list.append((loaded_score, name))
        return sorted(scores_list, key=lambda item: item[0], reverse=True)[:MAX_HIGH_SCORES]
    except (IOError, ValueError, PermissionError) as e: print(f"Error loading high scores: {e}", file=sys.stderr); return []
    except Exception as e: print(f"Unexpected error loading high scores: {e}", file=sys.stderr); traceback.print_exc(file=sys.stderr); return []

def save_high_scores(scores_list):
    try:
        sorted_scores = sorted(scores_list, key=lambda item: item[0], reverse=True)[:MAX_HIGH_SCORES]
        with open(HIGHSCORE_FILE, "w") as f:
            for hs_score, name in sorted_scores:
                safe_name = str(name).replace(',', '')[:MAX_NAME_LENGTH]
                f.write(f"{hs_score},{safe_name}\n")
    except (IOError, PermissionError) as e: print(f"Error saving high scores: {e}", file=sys.stderr)
    except Exception as e: print(f"Unexpected error saving high scores: {e}", file=sys.stderr); traceback.print_exc(file=sys.stderr)

def check_high_score(current_score_val, high_scores):
    if not high_scores or len(high_scores) < MAX_HIGH_SCORES: return True
    return current_score_val > high_scores[-1][0]

def get_name_input(stdscr, prompt, max_len):
    curses.curs_set(1); curses.echo(); stdscr.nodelay(False)
    sh, sw = stdscr.getmaxyx(); input_win_y = sh // 2 + 4
    prompt_len = len(prompt); total_width = prompt_len + max_len
    input_win_x = sw // 2 - total_width // 2
    if input_win_x < 0: input_win_x = 0
    input_field_start_x = input_win_x + prompt_len
    if input_field_start_x + max_len >= sw:
        input_win_x = max(0, sw - total_width - 1); input_field_start_x = input_win_x + prompt_len
    try:
        stdscr.addstr(input_win_y, 0, " " * (sw - 1))
        stdscr.addstr(input_win_y, input_win_x, prompt)
    except curses.error: pass
    stdscr.refresh()
    name_bytes = stdscr.getstr(input_win_y, input_field_start_x, max_len)
    name = name_bytes.decode('utf-8', 'ignore').strip()
    curses.noecho(); curses.curs_set(0); stdscr.nodelay(True)
    return name if name else "Anon"

# --- Helper Functions --- (init_colors, select_difficulty, place_item unchanged)
def init_colors():
    if curses.has_colors():
        curses.start_color(); curses.use_default_colors()
        try:
            curses.init_pair(DEFAULT_PAIR, curses.COLOR_GREEN, -1)
            curses.init_pair(FOOD_PAIR, curses.COLOR_YELLOW, -1)
            curses.init_pair(POWERUP_TYPE_1_PAIR, curses.COLOR_CYAN, -1)
            curses.init_pair(POWERUP_TYPE_2_PAIR, curses.COLOR_RED, -1)
            curses.init_pair(POWERUP_TYPE_3_PAIR, curses.COLOR_WHITE, -1)
            curses.init_pair(POWERUP_TYPE_4_PAIR, curses.COLOR_BLUE, -1)
            curses.init_pair(POWERUP_TYPE_5_PAIR, curses.COLOR_MAGENTA, -1)
            curses.init_pair(OBSTACLE_PAIR, curses.COLOR_RED, -1)
            curses.init_pair(METEOR_PAIR, curses.COLOR_YELLOW, -1)
            curses.init_pair(MAZE_FOOD_PAIR, curses.COLOR_CYAN, -1)
            curses.init_pair(SNAKE_FLASH_PAIR, curses.COLOR_WHITE, -1)
            curses.init_pair(ENEMY_SNAKE_PAIR, curses.COLOR_MAGENTA, -1)
            curses.init_pair(BALL_PAIR, curses.COLOR_RED, -1)
            curses.init_pair(MAZE_WALL_PAIR, curses.COLOR_WHITE, -1)
            curses.init_pair(MAZE_SNAKE_PAIR, curses.COLOR_YELLOW, -1)
            return True
        except curses.error as e: print(f"Warning: Failed color init: {e}", file=sys.stderr); return False
    return False

def select_difficulty(stdscr, has_colors):
    stdscr.clear(); sh, sw = stdscr.getmaxyx()
    title = "Select Difficulty:"; title_x = sw // 2 - len(title) // 2
    if title_x < 0: title_x = 0
    stdscr.addstr(sh // 2 - 4, title_x, title)
    row = sh // 2 - 2; keys = sorted(DIFFICULTY_LEVELS.keys()); options = []
    for key in keys:
        level = DIFFICULTY_LEVELS[key]; option_text = f"({key}) {level['name']}"
        option_x = sw // 2 - len(option_text) // 2;
        if option_x < 0: option_x = 0
        options.append((row, option_x, option_text)); row += 1
    quit_text = "(q) Quit"; quit_x = sw // 2 - len(quit_text) // 2
    if quit_x < 0: quit_x = 0
    options.append((row + 1, quit_x, quit_text))
    for r, c, text in options:
        try: stdscr.addstr(r, c, text)
        except curses.error: pass
    stdscr.refresh()
    while True:
        key = stdscr.getch(); choice = None
        if key != -1 and key < 256:
            try: choice = chr(key)
            except ValueError: pass
        if choice in DIFFICULTY_LEVELS: stdscr.clear(); return DIFFICULTY_LEVELS[choice], choice
        elif choice == 'q': return None, None

def place_item(window, snake_body, existing_items, max_attempts=50):
    sh, sw = window.getmaxyx(); min_y, max_y = 1, sh - 2; min_x, max_x = 1, sw - 2
    if max_y < min_y or max_x < min_x: return None
    item_pos = None; attempts = 0;
    free_cells = (max_y - min_y + 1) * (max_x - min_x + 1) - len(snake_body) - len(existing_items)
    realistic_max_attempts = max(10, free_cells if free_cells > 0 else 10)
    max_attempts = min(max_attempts, realistic_max_attempts)
    occupied_coords = set(snake_body)
    for item in existing_items:
        if isinstance(item, (tuple, list)) and len(item) >= 2: occupied_coords.add(item[0:2])
        elif isinstance(item, dict) and 'pos' in item and isinstance(item['pos'], (tuple, list)) and len(item['pos']) >= 2: occupied_coords.add(item['pos'][0:2])
        elif isinstance(item, dict) and 'maze_walls' in item and isinstance(item['maze_walls'], set): occupied_coords.update(item['maze_walls'])
        elif isinstance(item, dict) and 'blocks' in item and isinstance(item['blocks'], list): occupied_coords.update(item['blocks'])
    while item_pos is None and attempts < max_attempts:
        if max_y < min_y or max_x < min_x: return None
        try: ny = random.randint(min_y, max_y); nx = random.randint(min_x, max_x)
        except ValueError: return None
        potential_pos = (nx, ny)
        if potential_pos not in occupied_coords: item_pos = potential_pos
        attempts += 1
    return item_pos

# --- Maze Generation for Wide Corridors --- (Unchanged)
def generate_wide_maze(target_h, target_w, corridor_w=3):
    corridor_w = max(1, (corridor_w // 2) * 2 + 1)
    grid_h = max(3, (target_h // corridor_w // 2) * 2 + 1)
    grid_w = max(3, (target_w // corridor_w // 2) * 2 + 1)
    if grid_h * corridor_w > target_h or grid_w * corridor_w > target_w or grid_h < 3 or grid_w < 3:
         print(f"Warning: Maze gen fail - target({target_h}x{target_w}) too small for grid({grid_h}x{grid_w}) & corridor({corridor_w})", file=sys.stderr); return set(), set(), None, None
    coarse_maze = [[True] * grid_w for _ in range(grid_h)]; coarse_path_cells = set()
    start_ch = random.randint(0, grid_h // 2 - 1) * 2 + 1; start_cw = random.randint(0, grid_w // 2 - 1) * 2 + 1
    stack = [(start_ch, start_cw)]; coarse_maze[start_ch][start_cw] = False; coarse_path_cells.add((start_cw, start_ch))
    while stack:
        ch, cw = stack[-1]; neighbors = []
        for dh, dw in [(0, 2), (0, -2), (2, 0), (-2, 0)]:
            nh, nw = ch + dh, cw + dw
            if 0 < nh < grid_h and 0 < nw < grid_w and coarse_maze[nh][nw]:
                wh, ww = ch + dh // 2, cw + dw // 2; neighbors.append((nh, nw, wh, ww))
        if neighbors:
            nh, nw, wh, ww = random.choice(neighbors)
            coarse_maze[nh][nw] = False; coarse_path_cells.add((nw, nh)); coarse_maze[wh][ww] = False; coarse_path_cells.add((ww, wh)); stack.append((nh, nw))
        else: stack.pop()
    if not coarse_path_cells: return set(), set(), None, None
    full_maze_walls = set((x, y) for y in range(target_h) for x in range(target_w)); expanded_path = set(); corridor_offset = corridor_w // 2
    for cw, ch in coarse_path_cells:
        center_x = cw * corridor_w + corridor_offset; center_y = ch * corridor_w + corridor_offset
        for dy in range(-corridor_offset, corridor_offset + 1):
            for dx in range(-corridor_offset, corridor_offset + 1):
                px, py = center_x + dx, center_y + dy
                if 0 <= px < target_w and 0 <= py < target_h: expanded_path.add((px, py)); full_maze_walls.discard((px, py))
    boundary_cells = sorted([cell for cell in coarse_path_cells if cell[0] == 1 or cell[0] == grid_w - 2 or cell[1] == 1 or cell[1] == grid_h - 2])
    if len(boundary_cells) < 2: return full_maze_walls, expanded_path, None, None
    entrance_coarse = random.choice(boundary_cells); exit_candidates = [cell for cell in boundary_cells if cell != entrance_coarse]; exit_coarse = random.choice(exit_candidates) if exit_candidates else random.choice(boundary_cells)
    entrance_center_x = entrance_coarse[0] * corridor_w + corridor_offset; entrance_center_y = entrance_coarse[1] * corridor_w + corridor_offset; exit_center_x = exit_coarse[0] * corridor_w + corridor_offset; exit_center_y = exit_coarse[1] * corridor_w + corridor_offset
    entrance_coord = (entrance_center_x, entrance_center_y); exit_coord = (exit_center_x, exit_center_y)
    def carve_opening(coarse_cell, center_x, center_y):
        ccw, cch = coarse_cell
        if cch == 1: # Top
            for dx in range(-corridor_offset, corridor_offset + 1): full_maze_walls.discard((center_x + dx, 0))
        elif cch == grid_h - 2: # Bottom
            for dx in range(-corridor_offset, corridor_offset + 1): full_maze_walls.discard((center_x + dx, target_h - 1))
        elif ccw == 1: # Left
            for dy in range(-corridor_offset, corridor_offset + 1): full_maze_walls.discard((0, center_y + dy))
        elif ccw == grid_w - 2: # Right
            for dy in range(-corridor_offset, corridor_offset + 1): full_maze_walls.discard((target_w - 1, center_y + dy))
    carve_opening(entrance_coarse, entrance_center_x, entrance_center_y); carve_opening(exit_coarse, exit_center_x, exit_center_y)
    return full_maze_walls, expanded_path, entrance_coord, exit_coord

# --- Power-up Effect Management ---
def create_enemy_effect(segments, target_pos, end_time, move_delay=1):
    """Helper to create enemy effect dict."""
    # (Unchanged)
    return {'type': 5, 'end_time': end_time, 'start_time': time.time(), 'data': {'snake': segments, 'target': target_pos, 'move_delay': move_delay, 'move_counter': random.randint(0, max(0, move_delay -1))}}

def update_active_effects(stdscr, snake, current_timeout, difficulty_timeout):
    """Updates effects, returns state tuple including player_grew_from_enemy_hit."""
    # (Unchanged from v2.8 - includes new return value)
    global active_effects, ball_powerup_count, score, type1_food_spawn_count
    global last_type1_decrement_time, foods, maze_food_items
    global speed_increase_factor

    sh, sw = stdscr.getmaxyx(); current_time = time.time()
    new_timeout = current_timeout; expired_indices = []
    is_thick_active = False; active_obstacles = set(); active_maze_walls = set(); is_maze_active = False
    user_head = snake[0] if snake else None
    new_effects_to_add = []
    player_grew_from_enemy_hit = False # <<< Initialize flag

    if current_time - last_type1_decrement_time > TYPE1_DECREMENT_INTERVAL:
        if type1_food_spawn_count > 1: type1_food_spawn_count -= 1
        last_type1_decrement_time = current_time

    for i, effect in enumerate(active_effects):
        if current_time >= effect['end_time']:
            if i not in expired_indices: expired_indices.append(i)
            effect_type = effect['type']
            if effect_type in [1, 4, 8]:
                 original_timeout = effect['data'].get('original_timeout', difficulty_timeout)
                 new_timeout = max(MIN_TIMEOUT, min(MAX_TIMEOUT, original_timeout))
            elif effect_type == 5: pass
            elif effect_type == 8:
                maze_food_items.clear(); foods.clear()
                if snake:
                    new_food_pos = place_item(stdscr, snake, [])
                    if new_food_pos: foods.append(new_food_pos)
            continue

        effect_type = effect['type']; effect_data = effect.get('data', {})
        if effect_type == 1: pass
        elif effect_type == 2:
            new_balls = []; balls_data = effect_data.get('balls', [])
            if not balls_data:
                 if i not in expired_indices: expired_indices.append(i); continue
            for ball in balls_data:
                bx, by = ball['pos']; bdx, bdy = ball['vel']
                n_bx, n_by = bx + bdx, by + bdy
                if n_bx <= 0 or n_bx >= sw - 1: bdx *= -1; n_bx = bx
                if n_by <= 0 or n_by >= sh - 1: bdy *= -1; n_by = by
                final_bx = max(1, min(sw - 2, n_bx)); final_by = max(1, min(sh - 2, n_by))
                ball['pos'] = (final_bx, final_by); ball['vel'] = (bdx, bdy)
                new_balls.append(ball)
                if snake and ball['pos'] in snake:
                    if len(snake) > 1: snake.pop(); score = max(0, score + PENALTY_BALL)
            effect['data']['balls'] = new_balls
        elif effect_type == 3: is_thick_active = True
        elif effect_type == 4: pass
        elif effect_type == 6: active_obstacles.update(effect_data.get('blocks', []))
        elif effect_type == 7:
            new_meteors = []; meteors_data = effect_data.get('meteors', [])
            if not meteors_data:
                 if i not in expired_indices: expired_indices.append(i); continue
            for meteor in meteors_data:
                mx, my = meteor['pos']; mdx, mdy = meteor['vel']
                nmy = my + mdy; nmx = mx + mdx
                if not (0 <= nmx < sw): continue
                meteor['pos'] = (nmx, nmy)
                if snake and meteor['pos'] in snake:
                    if len(snake) > 1: snake.pop(); score = max(0, score + PENALTY_METEOR)
                if nmy < sh: new_meteors.append(meteor)
            effect['data']['meteors'] = new_meteors
        elif effect_type == 8: active_maze_walls.update(effect_data.get('maze_walls', [])); is_maze_active = True
        elif effect_type == 5: # Enemy Snake Logic
             if not snake: continue # Skip if player fractured last iteration
             user_head = snake[0] # Re-get head
             enemy_snake = effect_data.get('snake', [])
             if not enemy_snake:
                 if i not in expired_indices: expired_indices.append(i); continue

             enemy_head = enemy_snake[0]; last_pos = enemy_snake[1] if len(enemy_snake) > 1 else None
             move_delay = effect_data.get('move_delay', ENEMY_MOVE_DELAY_BASE); move_counter = effect_data.get('move_counter', 0) + 1
             moved = False; new_e_head = enemy_head

             if move_counter >= move_delay: # Move logic
                 effect_data['move_counter'] = 0; target_pos = snake[0]
                 ideal_dx, ideal_dy = 0, 0
                 if enemy_head[0] != target_pos[0]: ideal_dx = 1 if target_pos[0] > enemy_head[0] else -1
                 if enemy_head[1] != target_pos[1]: ideal_dy = 1 if target_pos[1] > enemy_head[1] else -1
                 if ideal_dx != 0 and ideal_dy != 0:
                     if abs(target_pos[0] - enemy_head[0]) > abs(target_pos[1] - enemy_head[1]): ideal_dy = 0
                     else: ideal_dx = 0
                 final_dx, final_dy = ideal_dx, ideal_dy
                 if random.random() < ENEMY_RANDOM_MOVE_CHANCE:
                     possible_wobbles = []
                     if ideal_dx != 0: possible_wobbles = [(0, 1), (0, -1)]
                     elif ideal_dy != 0: possible_wobbles = [(1, 0), (-1, 0)]
                     if not possible_wobbles or (ideal_dx == 0 and ideal_dy == 0) : possible_wobbles = [(0,1),(0,-1),(1,0),(-1,0)]
                     if possible_wobbles: final_dx, final_dy = random.choice(possible_wobbles)
                     else: final_dx, final_dy = ideal_dx, ideal_dy
                 next_e_x, next_e_y = enemy_head[0] + final_dx, enemy_head[1] + final_dy
                 potential_new_head = (next_e_x, next_e_y)
                 if potential_new_head != last_pos: new_e_head = potential_new_head
                 elif (enemy_head[0] + ideal_dx, enemy_head[1] + ideal_dy) != last_pos: new_e_head = (enemy_head[0] + ideal_dx, enemy_head[1] + ideal_dy)
                 if new_e_head != enemy_head:
                     moved = True; enemy_snake.insert(0, new_e_head)
                     if len(enemy_snake) > 1 and new_e_head != user_head: enemy_snake.pop()
             else: effect_data['move_counter'] = move_counter

             enemy_head = enemy_snake[0] # Update head pos
             collision_occurred = False

             # Collision Check 1: Enemy Head -> Player Body (Fracture)
             if not collision_occurred and snake and len(snake) > 1 and enemy_head in snake[1:]:
                 try:
                     collision_index = snake.index(enemy_head, 1)
                     print(f"Enemy ({i}) hit player body at index {collision_index}", file=sys.stderr)
                     original_len = len(snake); snake[:] = snake[:collision_index] # Modify global snake
                     print(f"Snake fractured from {original_len} to {len(snake)}", file=sys.stderr)
                     collision_occurred = True
                     if not snake: print("Snake empty after fracture!", file=sys.stderr) # Game over check needed in main
                 except ValueError: pass

             if not snake: continue # Skip rest if player died
             user_head = snake[0] # Update user head again

             # Collision Check 2: Player Head -> Enemy Head (Explosion)
             if not collision_occurred and user_head == enemy_head:
                 print(f"Head-on collision! Enemy {i} explodes.", file=sys.stderr)
                 for seg_x, seg_y in enemy_snake[1:]:
                     if 1 <= seg_x < sw-1 and 1 <= seg_y < sh-1: foods.append((seg_x, seg_y))
                 if i not in expired_indices: expired_indices.append(i)
                 collision_occurred = True; continue

             # Collision Check 3: Player Head -> Enemy Body (Split)
             if not collision_occurred and user_head in enemy_snake[1:]:
                 print(f"Player hit enemy {i} body! Splitting.", file=sys.stderr)
                 score += SCORE_FOOD
                 timeout_reduction = int(new_timeout * speed_increase_factor)
                 new_timeout = max(MIN_TIMEOUT, new_timeout - timeout_reduction)
                 player_grew_from_enemy_hit = True # <<< Signal growth >>>
                 try:
                     hit_index = enemy_snake.index(user_head)
                     first_half = enemy_snake[:hit_index]; second_half = enemy_snake[hit_index:]
                     remaining_end_time = effect['end_time']
                     if len(first_half) >= 1: new_effects_to_add.append( create_enemy_effect(first_half, snake[0], remaining_end_time, ENEMY_MOVE_DELAY_SPLIT) )
                     if len(second_half) >= 1: new_effects_to_add.append( create_enemy_effect(second_half, snake[0], remaining_end_time, ENEMY_MOVE_DELAY_SPLIT) )
                     if i not in expired_indices: expired_indices.append(i)
                     collision_occurred = True; continue
                 except ValueError: print(f"Error finding hit index for split: {user_head} in {enemy_snake}", file=sys.stderr)

             if not collision_occurred: effect['data']['snake'] = enemy_snake

    # Post-Loop Updates
    if new_effects_to_add: active_effects.extend(new_effects_to_add)
    if expired_indices:
        for i in sorted(expired_indices, reverse=True):
            if 0 <= i < len(active_effects): del active_effects[i]

    is_any_effect_active = len(active_effects) > 0
    is_thick_active = any(eff['type'] == 3 for eff in active_effects)
    is_maze_active = any(eff['type'] == 8 for eff in active_effects)
    new_timeout = max(MIN_TIMEOUT, min(MAX_TIMEOUT, new_timeout))

    return new_timeout, is_any_effect_active, is_thick_active, active_obstacles, active_maze_walls, is_maze_active, player_grew_from_enemy_hit


def draw_active_effects(stdscr, has_colors):
    """Draws visuals for active effects."""
    # (Unchanged from v2.7)
    global active_effects, maze_food_items
    sh, sw = stdscr.getmaxyx()
    obstacle_attrib = curses.color_pair(OBSTACLE_PAIR) if has_colors else 0
    meteor_attrib = curses.color_pair(METEOR_PAIR) if has_colors else 0
    maze_wall_attrib = curses.color_pair(MAZE_WALL_PAIR) if has_colors else 0
    maze_food_attrib = curses.color_pair(MAZE_FOOD_PAIR) if has_colors else 0
    ball_attrib = curses.color_pair(BALL_PAIR) if has_colors else 0
    enemy_attrib = curses.color_pair(ENEMY_SNAKE_PAIR) if has_colors else 0

    for effect in active_effects:
        effect_type = effect['type']; effect_data = effect.get('data', {})
        if effect_type == 2:
            for ball in effect_data.get('balls', []):
                bx, by = ball['pos'];
                if 0 <= by < sh and 0 <= bx < sw:
                    try: stdscr.addch(by, bx, BALL_SYMBOL, ball_attrib)
                    except curses.error: pass
        elif effect_type == 5:
             enemy_list = effect_data.get('snake', [])
             if enemy_list:
                 for seg in enemy_list:
                     ex, ey = seg;
                     if 0 <= ey < sh and 0 <= ex < sw:
                         try: stdscr.addch(ey, ex, ENEMY_SNAKE_SYMBOL, enemy_attrib)
                         except curses.error: pass
        elif effect_type == 6:
            for ox, oy in effect_data.get('blocks', []):
                if 0 <= oy < sh and 0 <= ox < sw:
                    try: stdscr.addch(oy, ox, OBSTACLE_SYMBOL, obstacle_attrib)
                    except curses.error: pass
        elif effect_type == 7:
            for meteor in effect_data.get('meteors', []):
                mx, my = meteor['pos']
                if 0 <= my < sh and 0 <= mx < sw:
                    try: stdscr.addch(my, mx, METEOR_SYMBOL, meteor_attrib)
                    except curses.error: pass
        elif effect_type == 8:
            for wx, wy in effect_data.get('maze_walls', []):
                if 0 <= wy < sh and 0 <= wx < sw:
                    try: stdscr.addch(wy, wx, WALL_SYMBOL, maze_wall_attrib)
                    except curses.error: pass
            for fx, fy in maze_food_items:
                if 0 <= fy < sh and 0 <= fx < sw:
                    try: stdscr.addch(fy, fx, FOOD_SYMBOL, maze_food_attrib)
                    except curses.error: pass

# --- Power-up Activation Logic --- (Unchanged from v2.8)
def activate_powerup(ptype, current_loop_time, stdscr, snake, current_timeout,
                     base_difficulty_timeout, powerup_slowdown_factor, difficulty_key, has_colors):
    """Handles activation logic. Returns new timeout. Sets flash message."""
    global active_effects, score, type1_food_spawn_count, ball_powerup_count
    global maze_food_items, foods, power_ups_on_screen
    global flash_message, flash_message_end_time

    if not snake: return current_timeout
    sh, sw = stdscr.getmaxyx()
    effect_duration = 0
    if ptype == 8:
        if isinstance(POWERUP_DURATIONS[8], dict): effect_duration = POWERUP_DURATIONS[8].get(difficulty_key, 45)
        else: print("Warning: POWERUP_DURATIONS[8] structure error", file=sys.stderr); effect_duration = 45
    elif ptype in POWERUP_DURATIONS:
        try: effect_duration = POWERUP_DURATIONS[ptype]()
        except TypeError: effect_duration = POWERUP_DURATIONS[ptype]
    else: print(f"Error: Duration missing for powerup {ptype}", file=sys.stderr); return current_timeout
    effect_end_time = current_loop_time + effect_duration
    new_effect = {'type': ptype, 'end_time': effect_end_time, 'data': {}, 'start_time': current_loop_time}
    activation_successful = True

    if ptype == 1:
        type1_food_spawn_count += 1; new_effect['data']['original_timeout'] = current_timeout
        timeout_increase = int(current_timeout * powerup_slowdown_factor); current_timeout = min(MAX_TIMEOUT, current_timeout + timeout_increase); stdscr.timeout(current_timeout)
        foods.clear(); all_items_to_avoid = power_ups_on_screen + list(set().union(*(eff['data'].get('blocks', set()) for eff in active_effects if eff['type'] == 6)))
        spawned_count = 0
        for _ in range(type1_food_spawn_count):
            new_food_pos = place_item(stdscr, snake, all_items_to_avoid)
            if new_food_pos: foods.append(new_food_pos); all_items_to_avoid.append(new_food_pos); spawned_count += 1
            else: break
        if spawned_count == 0 and type1_food_spawn_count > 0: print("Warning: No food spawned Type 1.", file=sys.stderr)
    elif ptype == 2:
        ball_powerup_count += 1; new_effect['data']['balls'] = []
        all_items_to_avoid = foods + power_ups_on_screen + list(set().union(*(eff['data'].get('blocks', set()) for eff in active_effects if eff['type'] == 6)))
        spawned_count = 0
        for _ in range(ball_powerup_count):
            ball_start_pos = place_item(stdscr, snake, all_items_to_avoid)
            if ball_start_pos:
                ball_vel = random.choice([(1,1), (1,-1), (-1,1), (-1,-1)]); new_effect['data']['balls'].append({'pos': ball_start_pos, 'vel': ball_vel})
                all_items_to_avoid.append({'pos': ball_start_pos}); spawned_count += 1
            else: break
        if spawned_count == 0 and ball_powerup_count > 0: print("Warning: No balls spawned Type 2.", file=sys.stderr); activation_successful = False
    elif ptype == 3: pass
    elif ptype == 4:
        new_effect['data']['original_timeout'] = current_timeout; current_timeout = MIN_TIMEOUT; stdscr.timeout(current_timeout)
    elif ptype == 5:
        start_edge = random.choice(['top', 'bottom', 'left', 'right']); sx, sy = 0, 0
        if start_edge == 'top': sx = random.randint(1, sw - 2); sy = 0
        elif start_edge == 'bottom': sx = random.randint(1, sw - 2); sy = sh - 1
        elif start_edge == 'left': sx = 0; sy = random.randint(1, sh - 2)
        else: sx = sw - 1; sy = random.randint(1, sh - 2)
        initial_segments = [(sx, sy)]; target_pos = snake[0] if snake else (sw//2, sh//2)
        new_effect = create_enemy_effect(initial_segments, target_pos, effect_end_time, ENEMY_MOVE_DELAY_BASE)
    elif ptype == 6:
        num_obstacles = max(1, len(snake) // 2); placed_obstacles = []
        all_items_to_avoid = foods + power_ups_on_screen
        current_obstacles_coords = set().union(*(eff['data'].get('blocks', set()) for eff in active_effects if eff['type'] == 6))
        all_items_to_avoid.extend(list(current_obstacles_coords))
        for _ in range(num_obstacles):
            pos = place_item(stdscr, snake, all_items_to_avoid, max_attempts=MAX_OBSTACLE_PLACEMENT_ATTEMPTS)
            if pos: placed_obstacles.append(pos); all_items_to_avoid.append(pos)
            else: print(f"Warning: Placed {len(placed_obstacles)}/{num_obstacles} obstacles.", file=sys.stderr); break
        min_required_obstacles = max(1, num_obstacles // 2) if num_obstacles > 0 else 0
        if num_obstacles > 0 and len(placed_obstacles) < min_required_obstacles:
            score = max(0, score + PENALTY_OBSTACLE_FAIL)
            if len(snake) > 1:
                segments_to_remove = max(1, len(snake) // 4)
                for _ in range(segments_to_remove):
                    if len(snake) > 1: snake.pop()
                    else: break
            activation_successful = False; print(f"Obstacle placement failed, penalty applied.", file=sys.stderr)
        elif placed_obstacles: new_effect['data']['blocks'] = placed_obstacles
        else: activation_successful = False
    elif ptype == 7:
        num_meteors = random.randint(max(1, sw // 15), max(3, sw // 10)); new_effect['data']['meteors'] = []
        for _ in range(num_meteors):
            m_start_x = random.randint(1, sw - 2); m_dx = random.choice([-1, 0, 0, 1])
            new_effect['data']['meteors'].append({'pos': (m_start_x, 0), 'vel': (m_dx, 1)})
    elif ptype == 8:
        max_maze_cells = int(sh * sw * MAZE_AREA_PERCENTAGE); approx_target_cells_1d = int(math.sqrt(max_maze_cells))
        target_h = max(5, approx_target_cells_1d); target_w = max(5, approx_target_cells_1d)
        target_h = min(target_h, sh - 2); target_w = min(target_w, sw - 2)
        offset_y = (sh - target_h) // 2; offset_x = (sw - target_w) // 2
        rel_maze_walls, rel_expanded_path, rel_entrance, rel_exit = generate_wide_maze(target_h, target_w, MAZE_CORRIDOR_WIDTH)
        if rel_expanded_path:
            offset_maze_walls = set((cx + offset_x, cy + offset_y) for cx, cy in rel_maze_walls)
            offset_expanded_path = set((cx + offset_x, cy + offset_y) for cx, cy in rel_expanded_path)
            offset_entrance = (rel_entrance[0] + offset_x, rel_entrance[1] + offset_y) if rel_entrance else None
            offset_exit = (rel_exit[0] + offset_x, rel_exit[1] + offset_y) if rel_exit else None
            if snake:
                head_pos = snake[0]
                if head_pos in offset_maze_walls: offset_maze_walls.discard(head_pos); print(f"Note: Cleared maze wall at snake start pos {head_pos}", file=sys.stderr)
            new_effect['data']['original_timeout'] = current_timeout
            current_timeout = min(MAX_TIMEOUT, int(current_timeout * MAZE_SLOWDOWN_FACTOR)); stdscr.timeout(current_timeout)
            available_offset_path = list(offset_expanded_path - set(snake))
            if not available_offset_path: maze_food_items = []
            else:
                num_maze_food = len(available_offset_path) // MAZE_FOOD_DENSITY
                if num_maze_food == 0 and len(available_offset_path) > 0: num_maze_food = 1
                num_maze_food = min(num_maze_food, len(available_offset_path))
                maze_food_coords_offset = random.sample(available_offset_path, num_maze_food); maze_food_items = list(maze_food_coords_offset)
            new_effect['data']['maze_walls'] = offset_maze_walls; new_effect['data']['maze_entrance'] = offset_entrance; new_effect['data']['maze_exit'] = offset_exit; foods.clear()
        else: activation_successful = False; print("Error: Wide maze generation failed.", file=sys.stderr)

    if activation_successful:
        if ptype != 5: active_effects.append(new_effect)
        else:
             if new_effect and new_effect.get('type') == 5: active_effects.append(new_effect)
             else: activation_successful = False; print("Warning: Failed to create initial enemy effect.", file=sys.stderr)
    if activation_successful:
        flash_message = POWERUP_NAMES.get(ptype, f"Power Up Type {ptype}!")
        flash_message_end_time = current_loop_time + FLASH_MESSAGE_DURATION
    else: print(f"Powerup type {ptype} activation cancelled.", file=sys.stderr)
    return current_timeout

# --- Game State Reset Function ---
def reset_game_state():
    """Resets global variables for starting a new game."""
    global score, active_effects, ball_powerup_count, type1_food_spawn_count
    global last_type1_decrement_time, key_press_history, maze_food_items
    global foods, power_ups_on_screen, flash_message, flash_message_end_time
    global last_flash_time, flash_on, maze_just_activated

    score = 0; active_effects = []; ball_powerup_count = 0
    type1_food_spawn_count = 3; last_type1_decrement_time = time.time()
    key_press_history.clear(); maze_food_items = []; foods = []
    power_ups_on_screen = []; flash_message = None; flash_message_end_time = 0
    flash_on = False; last_flash_time = time.time(); maze_just_activated = False

# --- Main Game Function ---
def main(stdscr, test_mode=False):
    """Initializes and runs the main game loop, allowing restarts."""
    global active_effects, score, last_flash_time, flash_on
    global key_press_history, maze_food_items, foods, power_ups_on_screen
    global flash_message, flash_message_end_time
    global maze_just_activated
    global speed_increase_factor # Make global

    # --- Initial Setup ---
    curses.curs_set(0); stdscr.nodelay(True); stdscr.keypad(True)
    sh, sw = stdscr.getmaxyx()
    min_h, min_w = 20, 50
    if sh < min_h or sw < min_w:
        # Raise custom exception if terminal is too small
        raise TerminalTooSmallError(f"Min: {min_w}x{min_h}, Has: {sw}x{sh}")

    has_colors = init_colors()
    flash_message_attrib = curses.color_pair(SNAKE_FLASH_PAIR) | curses.A_BOLD if has_colors else curses.A_BOLD
    maze_snake_attrib = curses.color_pair(MAZE_SNAKE_PAIR) | curses.A_BOLD if has_colors else curses.A_BOLD

    # --- Difficulty Selection ---
    difficulty, difficulty_key = select_difficulty(stdscr, has_colors)
    if difficulty is None: return
    base_difficulty_timeout = difficulty["timeout"]
    speed_increase_factor = difficulty["increase"] / 100.0 # Set global here
    powerup_slowdown_factor = difficulty["slowdown"] / 100.0

    # --- Outer Game Loop ---
    play_again = True
    while play_again:
        reset_game_state()
        current_timeout = base_difficulty_timeout
        stdscr.timeout(current_timeout)

        start_x, start_y = sw // 4, sh // 2
        snake = [(start_x, start_y), (start_x - 1, start_y), (start_x - 2, start_y)]
        direction = curses.KEY_RIGHT
        initial_food_pos = place_item(stdscr, snake, [])
        if initial_food_pos: foods.append(initial_food_pos)
        else: print("Warning: Could not place initial food.", file=sys.stderr)
        next_power_up_spawn_time = time.time() + random.uniform(15, 60)

        # --- Test Mode Activation ---
        if test_mode:
            print("--- TEST MODE: Activating all powerups ---", file=sys.stderr)
            current_activate_time = time.time(); test_mode_maze_activated_this_run = False
            for ptype_test in sorted(POWERUP_TYPES):
                powerup_activated = False # Track if this specific one activated
                # Count existing effects of this type before activation attempt
                initial_count = len([e for e in active_effects if e['type'] == ptype_test])
                current_timeout = activate_powerup( ptype_test, current_activate_time, stdscr, snake, current_timeout, base_difficulty_timeout, powerup_slowdown_factor, difficulty_key, has_colors)
                # Check if a new effect of this type exists now
                final_count = len([e for e in active_effects if e['type'] == ptype_test])
                if final_count > initial_count: powerup_activated = True

                stdscr.timeout(current_timeout)
                if ptype_test == 8 and powerup_activated: test_mode_maze_activated_this_run = True
            if test_mode_maze_activated_this_run:
                 print(f"Test Mode: Freezing for {MAZE_INITIAL_FREEZE_S}s...", file=sys.stderr)
                 stdscr.clear();
                 if snake: # Draw simple snake
                     snake_attr = maze_snake_attrib if has_colors else 0 # Assume maze color for test
                     for seg_x, seg_y in snake:
                         if 0 <= seg_y < sh and 0 <= seg_x < sw: stdscr.addch(seg_y, seg_x, SNAKE_SYMBOL, snake_attr)
                 draw_active_effects(stdscr, has_colors); stdscr.refresh()
                 time.sleep(MAZE_INITIAL_FREEZE_S); curses.flushinp()
            print("--- Test mode activation complete ---", file=sys.stderr)


        # --- Inner Game Loop ---
        game_over = False; quit_game = False
        while not game_over and not quit_game:
            current_loop_time = time.time(); grew_from_eating = False

            if maze_just_activated:
                time.sleep(MAZE_INITIAL_FREEZE_S); curses.flushinp(); maze_just_activated = False

            # 1. Input Handling
            key = stdscr.getch(); new_direction = direction
            if key == curses.KEY_LEFT and direction != curses.KEY_RIGHT: new_direction = curses.KEY_LEFT
            elif key == curses.KEY_RIGHT and direction != curses.KEY_LEFT: new_direction = curses.KEY_RIGHT
            elif key == curses.KEY_UP and direction != curses.KEY_DOWN: new_direction = curses.KEY_UP
            elif key == curses.KEY_DOWN and direction != curses.KEY_UP: new_direction = curses.KEY_DOWN
            elif key == ord('q'): quit_game = True; continue
            elif key == ord('x'): key_press_history.append('x')
            elif key != -1: key_press_history.clear()
            direction = new_direction

            # 2. Secret Code Activation ('xxx')
            is_maze_already_active_check = any(eff['type'] == 8 for eff in active_effects)
            if list(key_press_history) == ['x', 'x', 'x'] and not is_maze_already_active_check:
                initial_maze_effects = len([e for e in active_effects if e['type'] == 8])
                current_timeout = activate_powerup(8, current_loop_time, stdscr, snake, current_timeout, base_difficulty_timeout, powerup_slowdown_factor, difficulty_key, has_colors)
                final_maze_effects = len([e for e in active_effects if e['type'] == 8])
                if final_maze_effects > initial_maze_effects: maze_just_activated = True
                stdscr.timeout(current_timeout); key_press_history.clear()

            # 3. Update Active Power-up Effects
            current_timeout, is_any_effect_active, is_thick_active, \
            active_obstacles, active_maze_walls, is_maze_active, \
            player_grew_from_enemy_hit = \
                update_active_effects(stdscr, snake, current_timeout, base_difficulty_timeout)
            stdscr.timeout(current_timeout)

            # 4. Check for Game Over
            if not snake: game_over = True; continue

            # 5. Snake Color / Flashing Logic
            snake_attrib = 0
            if has_colors:
                if is_maze_active: snake_attrib = maze_snake_attrib
                elif is_any_effect_active:
                    if current_loop_time - last_flash_time > FLASH_INTERVAL: flash_on = not flash_on; last_flash_time = current_loop_time
                    snake_attrib = curses.color_pair(SNAKE_FLASH_PAIR if flash_on else DEFAULT_PAIR)
                else: snake_attrib = curses.color_pair(DEFAULT_PAIR); flash_on = False

            # 6. Calculate Snake's Next Head Position
            if not snake: game_over = True; continue
            head_x, head_y = snake[0]
            if direction == curses.KEY_RIGHT: head_x += 1
            elif direction == curses.KEY_LEFT: head_x -= 1
            elif direction == curses.KEY_UP: head_y -= 1
            elif direction == curses.KEY_DOWN: head_y += 1
            new_head = (head_x, head_y)

            # 7. Check Collisions
            wall_hit = head_x < 0 or head_x >= sw or head_y < 0 or head_y >= sh
            self_collision = len(snake) > 1 and new_head in snake[1:]
            obstacle_hit = new_head in active_obstacles
            maze_wall_hit = new_head in active_maze_walls
            if wall_hit or self_collision or obstacle_hit or maze_wall_hit:
                game_over = True; continue

            # 8. Move Snake
            snake.insert(0, new_head)

            # 9. Food Consumption
            food_list_to_check = maze_food_items if is_maze_active else foods
            food_to_remove_index = -1
            for i, food_pos in enumerate(food_list_to_check):
                if new_head == food_pos:
                    grew_from_eating = True; food_to_remove_index = i
                    score += SCORE_MAZE_FOOD if is_maze_active else SCORE_FOOD
                    if not is_maze_active:
                        timeout_reduction = int(current_timeout * speed_increase_factor)
                        current_timeout = max(MIN_TIMEOUT, current_timeout - timeout_reduction)
                        stdscr.timeout(current_timeout)
                    break
            if food_to_remove_index != -1:
                del food_list_to_check[food_to_remove_index]
                if not is_maze_active:
                    all_items_on_screen = foods + power_ups_on_screen + list(active_obstacles) + maze_food_items + list(active_maze_walls)
                    new_food_pos = place_item(stdscr, snake, all_items_on_screen)
                    if new_food_pos: foods.append(new_food_pos)
                    else: print("Warning: Could not place new food.", file=sys.stderr)

            # 10. Power-up Consumption
            powerup_to_remove_index = -1; consumed_powerup_type = -1
            if not grew_from_eating and not is_maze_active:
                for i, (px, py, ptype) in enumerate(power_ups_on_screen):
                    if new_head == (px, py):
                        grew_from_eating = True; powerup_to_remove_index = i
                        consumed_powerup_type = ptype; score += SCORE_POWERUP; break
            if consumed_powerup_type != -1:
                initial_maze_count = len([e for e in active_effects if e['type'] == 8])
                del power_ups_on_screen[powerup_to_remove_index]
                current_timeout = activate_powerup( consumed_powerup_type, current_loop_time, stdscr, snake, current_timeout, base_difficulty_timeout, powerup_slowdown_factor, difficulty_key, has_colors)
                final_maze_count = len([e for e in active_effects if e['type'] == 8])
                if consumed_powerup_type == 8 and final_maze_count > initial_maze_count: maze_just_activated = True
                stdscr.timeout(current_timeout)

            # 11. Pop Tail (Corrected)
            if not grew_from_eating and not player_grew_from_enemy_hit:
                if len(snake) > 0: snake.pop()

            if not snake: game_over = True; continue

            # 12. Power-up Spawning
            if not is_maze_active and current_loop_time >= next_power_up_spawn_time:
                max_powerups = 5
                if len(power_ups_on_screen) < max_powerups:
                    ptype = random.choice(POWERUP_TYPES)
                    all_items = foods + power_ups_on_screen + list(active_obstacles) + maze_food_items + list(active_maze_walls)
                    pos = place_item(stdscr, snake, all_items)
                    if pos: power_ups_on_screen.append((*pos, ptype))
                next_power_up_spawn_time = current_loop_time + random.uniform(10, 40)

            # --- 13. Drawing ---
            stdscr.clear()
            snake_len = len(snake) if snake else 0 # Length for status
            status_line = f"Score: {score} | Speed: {current_timeout}ms | Len: {snake_len}"
            try: stdscr.addstr(0, 1, status_line[:sw-1])
            except curses.error: pass
            countdown_row = 1; active_timed_effects_info = []
            for effect in active_effects:
                 if effect['type'] in TIMED_EFFECTS_TO_DISPLAY:
                     time_remaining = effect['end_time'] - current_loop_time
                     if time_remaining > 0: name = POWERUP_NAMES.get(effect['type'], f"Effect {effect['type']}"); active_timed_effects_info.append(f"{name}: {time_remaining:.1f}s")
            for info_line in active_timed_effects_info:
                 if countdown_row < sh -1:
                     try: stdscr.addstr(countdown_row, 1, info_line[:sw-1])
                     except curses.error: pass; countdown_row += 1
                 else: break
            if snake: # Draw snake
                thick_attrib = curses.color_pair(DEFAULT_PAIR) if has_colors else 0; drawn_thick_segments = set()
                for i, segment in enumerate(snake):
                    seg_x, seg_y = segment
                    try:
                        if 0 <= seg_y < sh and 0 <= seg_x < sw: stdscr.addch(seg_y, seg_x, SNAKE_SYMBOL, snake_attrib)
                    except curses.error: pass
                    if is_thick_active and i < len(snake) - 1:
                        next_segment = snake[i+1]; dx = segment[0]-next_segment[0]; dy = segment[1]-next_segment[1]
                        adj_x, adj_y = seg_x, seg_y
                        if dx != 0: adj_y += 1
                        elif dy != 0: adj_x += 1
                        adj_pos = (adj_x, adj_y)
                        if adj_pos not in drawn_thick_segments:
                            if 0 <= adj_y < sh and 0 <= adj_x < sw:
                                try: stdscr.addch(adj_y, adj_x, THICK_SNAKE_EXTRA_SYMBOL, thick_attrib); drawn_thick_segments.add(adj_pos)
                                except curses.error: pass
            if not is_maze_active: # Draw regular food
                food_attrib = curses.color_pair(FOOD_PAIR) if has_colors else 0
                for fx, fy in foods:
                    try:
                        if 0 <= fy < sh and 0 <= fx < sw: stdscr.addch(fy, fx, FOOD_SYMBOL, food_attrib)
                    except curses.error: pass
            for px, py, ptype in power_ups_on_screen: # Draw powerup pickups
                pup_symbol = UNIFIED_POWERUP_SYMBOL
                pup_color_id_name = f"POWERUP_TYPE_{ptype}_PAIR"
                if ptype == 6: pup_color_id_name = "OBSTACLE_PAIR"
                elif ptype == 7: pup_color_id_name = "METEOR_PAIR"
                elif ptype == 8: pup_color_id_name = "MAZE_FOOD_PAIR"
                pup_color_id = globals().get(pup_color_id_name, DEFAULT_PAIR)
                pup_attrib = curses.color_pair(pup_color_id) if has_colors else 0
                try:
                    if 0 <= py < sh and 0 <= px < sw: stdscr.addch(py, px, pup_symbol, pup_attrib)
                except curses.error: pass
            draw_active_effects(stdscr, has_colors) # Draw effect visuals (maze walls/food etc)
            if flash_message and current_loop_time < flash_message_end_time: # Draw flash message
                msg_len = len(flash_message); msg_y = sh // 2 ; msg_x = sw // 2 - msg_len // 2
                if msg_x < 0: msg_x = 0
                try:
                     if 0 <= msg_y < sh: display_msg = flash_message[:max(0, sw - 1 - msg_x)]; stdscr.addstr(msg_y, msg_x, display_msg, flash_message_attrib)
                except curses.error: pass
            elif flash_message and current_loop_time >= flash_message_end_time: flash_message = None
            stdscr.refresh()
        # --- End of Inner Game Loop ---

        # --- Game Over Sequence ---
        if quit_game: play_again = False; continue
        curses.flushinp(); stdscr.nodelay(False); stdscr.clear()
        msg = f"Game Over! Final Score: {score}"; msg_y = sh // 2 - 6 ; msg_x = sw // 2 - len(msg) // 2
        try: stdscr.addstr(max(0, msg_y), max(0, msg_x), msg)
        except curses.error: pass
        high_scores = load_high_scores(); is_high = check_high_score(score, high_scores)
        if is_high:
            prompt = "New High Score! Enter Name: "; player_name = get_name_input(stdscr, prompt, MAX_NAME_LENGTH)
            high_scores.append((score, player_name)); save_high_scores(high_scores)
            high_scores_to_display = sorted(high_scores, key=lambda item: item[0], reverse=True)[:MAX_HIGH_SCORES]
        else: high_scores_to_display = high_scores
        hs_title = "High Scores:"; title_y = msg_y + 2; title_x = sw // 2 - len(hs_title) // 2
        try: stdscr.addstr(max(0, title_y), max(0, title_x), hs_title)
        except curses.error: pass
        score_start_y = title_y + 1; score_y_offset = 0
        for i, (hs_score, hs_name) in enumerate(high_scores_to_display):
            score_line = f"{i + 1}. {hs_name} - {hs_score}"; line_y = score_start_y + i; line_x = sw // 2 - len(score_line) // 2
            if line_y < sh - 2:
                 try: stdscr.addstr(line_y, max(0, line_x), score_line)
                 except curses.error: pass
            score_y_offset = i
        last_element_y = score_start_y + score_y_offset
        prompt_y = last_element_y + 2; prompt_text = "Play Again? (y/n)"; prompt_x = sw // 2 - len(prompt_text) // 2
        if prompt_y < sh:
             try: stdscr.addstr(prompt_y, max(0, prompt_x), prompt_text)
             except curses.error: pass
        stdscr.refresh()
        while True: # Wait for y/n
            final_key = stdscr.getch()
            if final_key == ord('y') or final_key == ord('Y'): play_again = True; stdscr.clear(); stdscr.nodelay(True); break
            elif final_key == ord('n') or final_key == ord('N') or final_key == ord('q'): play_again = False; break
    # --- End of Outer Play Again Loop ---


# --- Run the Game Entry Point ---
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Snake Game with Advanced Powerups')
    parser.add_argument('-t', '--test', action='store_true', help='Run in test mode.')
    args, unknown = parser.parse_known_args()
    run_test_mode = args.test

    final_message = "\nGame exited." # Default exit message
    try:
        curses.wrapper(main, run_test_mode)
    except TerminalTooSmallError as e: # Catch specific size error
        final_message = f"\nError: Terminal too small ({e})"
    except curses.error as e:
        final_message = f"\nA curses error occurred: {e}\nTry resizing terminal or using a different emulator."
        print("\n---------------------", file=sys.stderr); print(final_message, file=sys.stderr); print("---------------------\n", file=sys.stderr)
    except Exception as e:
        final_message = f"\nAn unexpected error occurred: {type(e).__name__}: {e}"
        print("\n---------------------", file=sys.stderr); print(final_message, file=sys.stderr); print("---------------------\n", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
    finally:
        # This runs after curses.wrapper has restored the terminal
        print(final_message)
