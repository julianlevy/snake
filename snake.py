# -*- coding: utf-8 -*- # Ensure unicode symbols work
# ==============================================================================
# Advanced Snake Game with Curses (v2.7 - Maze Entry & Interaction Fixes)
# ==============================================================================
# Features:
# - ... (previous features) ...
# - Maze Challenge (Type 8):
#   - Generates a small maze structure with wide (3-unit) corridors.
#   - Maze occupies <= 20% of screen area.
#   - Maze has designated entrance and exit (wall openings carved at index 1/dim-2).
#   - Snake color changes to bright Yellow within the maze.
#   - Fills ~1/4th of the maze path cells with food (spawning logic implemented).
#   - Duration depends on difficulty (Easy: 30s, Med: 45s, Hard: 60s).
#   - Game freezes for 3 seconds when maze first appears.
#   - Slows game speed significantly (MAZE_SLOWDOWN_FACTOR).
#   - Enemies and Meteors now collide with maze walls.
# - Thick Snake can now collect food with its extra segment.
# - Improved feedback if maze generation fails.
# ==============================================================================

import curses
import time
import random
import os
import collections
import argparse
import sys
import traceback
import math # For size calculations

# --- Constants ---

# Game Element Symbols
FOOD_SYMBOL = '#'
SNAKE_SYMBOL = '*'
WALL_SYMBOL = '%'
OBSTACLE_SYMBOL = '@'
ENEMY_SNAKE_SYMBOL = 'X'
METEOR_SYMBOL = '*'
BALL_SYMBOL = 'o'
THICK_SNAKE_EXTRA_SYMBOL = '+'
UNIFIED_POWERUP_SYMBOL = '?'
# Use different symbols for entrance/exit? Or just leave gaps? Leave gaps for now.
# MAZE_ENTRANCE_SYMBOL = '>'
# MAZE_EXIT_SYMBOL = '<'

# Powerup Types and Names
POWERUP_NAMES = {
    1: "Multi-Food & Slowdown", 2: "Bouncing Balls", 3: "Thick Snake", 4: "MAX SPEED",
    5: "Enemy Snake", 6: "Obstacle Blocks", 7: "Meteor Rain", 8: "Wide Maze" # Updated name
}
POWERUP_TYPES = list(POWERUP_NAMES.keys())
POWERUP_SYMBOLS = {ptype: UNIFIED_POWERUP_SYMBOL for ptype in POWERUP_TYPES}


# Speed & Timing Configuration
MIN_TIMEOUT = 25
MAX_TIMEOUT = 300
FLASH_INTERVAL = 0.15
TYPE1_DECREMENT_INTERVAL = 180
FLASH_MESSAGE_DURATION = 2.0
MAZE_INITIAL_FREEZE_S = 3
MAZE_SLOWDOWN_FACTOR = 3.0
MAZE_AREA_PERCENTAGE = 0.20 # Max 20% of screen area
MAZE_CORRIDOR_WIDTH = 3      # Width of maze paths
MAZE_FOOD_DENSITY = 4        # Place food approx every 4 path cells

# High Score Config (Unchanged)
HIGHSCORE_FILE = "snake_highscore.txt"
MAX_HIGH_SCORES = 5; MAX_NAME_LENGTH = 10

# Color Pair IDs
DEFAULT_PAIR = 1; FOOD_PAIR = 2
POWERUP_TYPE_1_PAIR = 3; POWERUP_TYPE_2_PAIR = 4; POWERUP_TYPE_3_PAIR = 5
POWERUP_TYPE_4_PAIR = 6; POWERUP_TYPE_5_PAIR = 7
OBSTACLE_PAIR = 11; POWERUP_TYPE_6_PAIR = OBSTACLE_PAIR
METEOR_PAIR = 12; POWERUP_TYPE_7_PAIR = METEOR_PAIR
MAZE_FOOD_PAIR = 14; POWERUP_TYPE_8_PAIR = MAZE_FOOD_PAIR
SNAKE_FLASH_PAIR = 8; ENEMY_SNAKE_PAIR = 9; BALL_PAIR = 10
MAZE_WALL_PAIR = 13; MAZE_SNAKE_PAIR = 16 # Yellow snake in maze

# Difficulty Levels (Unchanged)
DIFFICULTY_LEVELS = {
    "1": {"name": "Easy", "timeout": 150, "increase": 2, "slowdown": 60},
    "2": {"name": "Medium", "timeout": 100, "increase": 4, "slowdown": 45},
    "3": {"name": "Hard", "timeout": 70, "increase": 7, "slowdown": 30},
}

# Power-up Durations (Unchanged)
POWERUP_DURATIONS = {
    1: lambda: random.uniform(20, 40), 2: lambda: 8, 3: lambda: 10, 4: lambda: 5,
    5: lambda: 30, 6: lambda: 60, 7: lambda: 7,
    8: {"1": 30, "2": 45, "3": 60}
}
TIMED_EFFECTS_TO_DISPLAY = {1, 2, 3, 4, 5, 7, 8}

# Power-up Specific Consts (Unchanged)
BALL_MAX_SPEED = 1; ENEMY_RANDOM_MOVE_CHANCE = 0.20; ENEMY_INTERNAL_TIMEOUT = 15
MAX_OBSTACLE_PLACEMENT_ATTEMPTS = 100

# Score Constants (Unchanged)
SCORE_FOOD = 10; SCORE_MAZE_FOOD = 15; SCORE_POWERUP = 25; SCORE_ENEMY_HEAD = 100
PENALTY_BALL = -5; PENALTY_ENEMY_BODY = -20; PENALTY_METEOR = -2; PENALTY_OBSTACLE_FAIL = -15

# --- Global State Variables --- (Unchanged)
active_effects = []; last_flash_time = 0; flash_on = False; ball_powerup_count = 0
type1_food_spawn_count = 0; last_type1_decrement_time = 0
key_press_history = collections.deque(maxlen=3); maze_food_items = []; foods = []
power_ups_on_screen = []; score = 0; flash_message = None; flash_message_end_time = 0
maze_just_activated = False


# --- High Score Functions --- (Unchanged)
def load_high_scores():
    """Loads high scores from file."""
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
    """Saves high scores to file."""
    try:
        sorted_scores = sorted(scores_list, key=lambda item: item[0], reverse=True)[:MAX_HIGH_SCORES]
        with open(HIGHSCORE_FILE, "w") as f:
            for hs_score, name in sorted_scores:
                safe_name = str(name).replace(',', '')[:MAX_NAME_LENGTH]
                f.write(f"{hs_score},{safe_name}\n")
    except (IOError, PermissionError) as e: print(f"Error saving high scores: {e}", file=sys.stderr)
    except Exception as e: print(f"Unexpected error saving high scores: {e}", file=sys.stderr); traceback.print_exc(file=sys.stderr)

def check_high_score(current_score_val, high_scores):
    """Checks if the current score is a high score."""
    if not high_scores or len(high_scores) < MAX_HIGH_SCORES: return True
    return current_score_val > high_scores[-1][0]

def get_name_input(stdscr, prompt, max_len):
    """Gets player name input after game over."""
    curses.curs_set(1); curses.echo(); stdscr.nodelay(False)
    sh, sw = stdscr.getmaxyx(); input_win_y = sh // 2 + 4
    prompt_len = len(prompt); total_width = prompt_len + max_len
    input_win_x = sw // 2 - total_width // 2
    if input_win_x < 0: input_win_x = 0
    input_field_start_x = input_win_x + prompt_len
    if input_field_start_x + max_len >= sw:
        input_win_x = max(0, sw - total_width - 1); input_field_start_x = input_win_x + prompt_len
    try:
        stdscr.addstr(input_win_y, 0, " " * (sw - 1)) # Clear line
        stdscr.addstr(input_win_y, input_win_x, prompt)
    except curses.error: pass # Ignore errors drawing at screen edge
    stdscr.refresh()
    name_bytes = b""
    try:
         name_bytes = stdscr.getstr(input_win_y, input_field_start_x, max_len)
    except curses.error: pass # Ignore input errors
    name = name_bytes.decode('utf-8', 'ignore').strip()
    curses.noecho(); curses.curs_set(0); stdscr.nodelay(True)
    return name if name else "Anon"

# --- Helper Functions ---
def init_colors():
    """Initializes curses color pairs. Returns True on success."""
    if curses.has_colors():
        curses.start_color(); curses.use_default_colors()
        try:
            # Standard pairs
            curses.init_pair(DEFAULT_PAIR, curses.COLOR_GREEN, -1)
            curses.init_pair(FOOD_PAIR, curses.COLOR_YELLOW, -1)
            # Powerup pickup colors (used for '?')
            curses.init_pair(POWERUP_TYPE_1_PAIR, curses.COLOR_CYAN, -1)
            curses.init_pair(POWERUP_TYPE_2_PAIR, curses.COLOR_RED, -1)
            curses.init_pair(POWERUP_TYPE_3_PAIR, curses.COLOR_WHITE, -1)
            curses.init_pair(POWERUP_TYPE_4_PAIR, curses.COLOR_BLUE, -1)
            curses.init_pair(POWERUP_TYPE_5_PAIR, curses.COLOR_MAGENTA, -1)
            # Powerups using effect element colors
            curses.init_pair(OBSTACLE_PAIR, curses.COLOR_RED, -1) # Type 6 uses this
            curses.init_pair(METEOR_PAIR, curses.COLOR_YELLOW, -1) # Type 7 uses this
            curses.init_pair(MAZE_FOOD_PAIR, curses.COLOR_CYAN, -1) # Type 8 uses this
            # Other elements/states
            curses.init_pair(SNAKE_FLASH_PAIR, curses.COLOR_WHITE, -1) # Snake flash & message flash
            curses.init_pair(ENEMY_SNAKE_PAIR, curses.COLOR_MAGENTA, -1)
            curses.init_pair(BALL_PAIR, curses.COLOR_RED, -1)
            curses.init_pair(MAZE_WALL_PAIR, curses.COLOR_WHITE, -1)
            curses.init_pair(MAZE_SNAKE_PAIR, curses.COLOR_YELLOW, -1) # Snake in maze color
            return True
        except curses.error as e:
            print(f"Warning: Failed to initialize some/all color pairs: {e}", file=sys.stderr); return False
    return False

def select_difficulty(stdscr, has_colors):
    """Displays difficulty menu, returns tuple (difficulty_dict, difficulty_key) or (None, None)."""
    # (Unchanged from v2.6)
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
        except curses.error: pass # Ignore errors drawing at screen edge
    stdscr.refresh()
    while True:
        key = stdscr.getch(); choice = None
        if key != -1 and key < 256:
            try: choice = chr(key)
            except ValueError: pass
        if choice in DIFFICULTY_LEVELS: stdscr.clear(); return DIFFICULTY_LEVELS[choice], choice
        elif choice == 'q': return None, None

def place_item(window, snake_body, existing_items, max_attempts=50):
    """Finds random empty spot (x,y) excluding borders. Returns tuple or None."""
    # (Unchanged from v2.6 - Includes logic to avoid items like maze walls if passed in existing_items)
    sh, sw = window.getmaxyx(); min_y, max_y = 1, sh - 2; min_x, max_x = 1, sw - 2
    if max_y < min_y or max_x < min_x: return None # Playable area too small
    item_pos = None; attempts = 0;
    # Calculate a realistic max attempts based on estimated free cells
    free_cells = (max_y - min_y + 1) * (max_x - min_x + 1) - len(snake_body) - len(existing_items)
    realistic_max_attempts = max(10, free_cells // 2 if free_cells > 20 else 10) # Avoid excessive attempts if area is crowded
    max_attempts = min(max_attempts, realistic_max_attempts)

    occupied_coords = set(snake_body)
    # Add coordinates from various types of items in existing_items
    for item in existing_items:
        if isinstance(item, (tuple, list)) and len(item) >= 2 and all(isinstance(n, int) for n in item[:2]):
             occupied_coords.add(item[0:2]) # Simple (x,y) tuple/list like food
        elif isinstance(item, dict):
            if 'pos' in item and isinstance(item['pos'], (tuple, list)) and len(item['pos']) >= 2:
                occupied_coords.add(item['pos'][0:2]) # e.g., ball {'pos': (x,y), ...}
            elif 'blocks' in item and isinstance(item['blocks'], (set, list)):
                occupied_coords.update(item['blocks']) # e.g., obstacle effect {'blocks': {(x,y),...}}
            elif 'maze_walls' in item and isinstance(item['maze_walls'], (set, list)):
                occupied_coords.update(item['maze_walls']) # e.g., maze effect {'maze_walls': {(x,y),...}}
            elif 'snake' in item and isinstance(item['snake'], list): # Avoid placing on enemy snake
                 occupied_coords.update(item['snake'])

    while item_pos is None and attempts < max_attempts:
        if max_y < min_y or max_x < min_x: return None # Check again in case screen resized?
        try:
            ny = random.randint(min_y, max_y)
            nx = random.randint(min_x, max_x)
        except ValueError: return None # If min > max due to tiny screen

        potential_pos = (nx, ny)
        if potential_pos not in occupied_coords:
            item_pos = potential_pos
        attempts += 1

    # if not item_pos and free_cells > 0:
    #     print(f"Warning: place_item failed after {attempts} attempts despite {free_cells} estimated free cells.", file=sys.stderr)
    # elif not item_pos:
    #      print(f"Warning: place_item failed, likely no free space.", file=sys.stderr)

    return item_pos


# --- New Maze Generation for Wide Corridors ---
def generate_wide_maze(target_h, target_w, corridor_w=3):
    """
    Generates a maze structure with corridors of specified width.
    Uses DFS on a coarse grid, then expands paths and carves walls.
    Returns (set_of_wall_coords, set_of_path_coords, entrance_coord, exit_coord)
    relative to a 0,0 origin for the target_h x target_w area.
    Returns empty sets and None coords if generation fails.

    FIX: Carves openings at index 1 or target_dim-2 to align with playable area.
    """
    # Ensure corridor width is odd and >= 1
    corridor_w = max(1, (corridor_w // 2) * 2 + 1)

    # Calculate coarse grid dimensions
    grid_h = max(3, (target_h // corridor_w // 2) * 2 + 1)
    grid_w = max(3, (target_w // corridor_w // 2) * 2 + 1)

    # Check if target dimensions are feasible for the grid and corridor width
    # Need at least 3 cells high/wide in target for carving at index 1 and dim-2
    if target_h < 3 or target_w < 3 or grid_h * corridor_w > target_h or grid_w * corridor_w > target_w:
        print(f"Warning: Maze gen fail - target area {target_h}x{target_w} too small for grid {grid_h}x{grid_w} & corridor {corridor_w}", file=sys.stderr)
        return set(), set(), None, None

    # 1. Run DFS on the coarse grid
    coarse_maze = [[True] * grid_w for _ in range(grid_h)] # True = Wall
    coarse_path_cells = set() # Store (col, row) of coarse path cells

    start_ch = random.randint(0, grid_h // 2 - 1) * 2 + 1
    start_cw = random.randint(0, grid_w // 2 - 1) * 2 + 1
    stack = [(start_ch, start_cw)]
    coarse_maze[start_ch][start_cw] = False # Mark as path
    coarse_path_cells.add((start_cw, start_ch))

    while stack:
        ch, cw = stack[-1]; neighbors = []
        # Check potential neighbors (2 cells away)
        for dh, dw in [(0, 2), (0, -2), (2, 0), (-2, 0)]:
            nh, nw = ch + dh, cw + dw
            # Check bounds and if neighbor is a wall (unvisited)
            if 0 < nh < grid_h and 0 < nw < grid_w and coarse_maze[nh][nw]:
                wh, ww = ch + dh // 2, cw + dw // 2 # Wall between current and neighbor
                neighbors.append((nh, nw, wh, ww))

        if neighbors:
            nh, nw, wh, ww = random.choice(neighbors)
            coarse_maze[nh][nw] = False; coarse_path_cells.add((nw, nh)) # Mark neighbor as path
            coarse_maze[wh][ww] = False; coarse_path_cells.add((ww, wh)) # Mark wall between as path
            stack.append((nh, nw))
        else:
            stack.pop() # Backtrack

    if not coarse_path_cells: return set(), set(), None, None # Should not happen if grid >= 3x3

    # 2. Expand coarse path to full grid and define walls/paths
    # Initialize full grid as all walls
    full_maze_walls = set((x, y) for y in range(target_h) for x in range(target_w))
    expanded_path = set()

    corridor_offset = corridor_w // 2

    # Iterate through coarse path cells (including walls carved between cells)
    for cw, ch in coarse_path_cells:
        center_x = cw * corridor_w + corridor_offset
        center_y = ch * corridor_w + corridor_offset
        # Carve out the corridor_w x corridor_w block for this path cell
        for dy in range(-corridor_offset, corridor_offset + 1):
            for dx in range(-corridor_offset, corridor_offset + 1):
                px, py = center_x + dx, center_y + dy
                if 0 <= px < target_w and 0 <= py < target_h:
                    expanded_path.add((px, py))
                    full_maze_walls.discard((px, py)) # Remove path from walls

    # 3. Define Entrance and Exit on the boundary of the coarse grid
    # Boundary cells are path cells adjacent to the coarse grid edge (index 1 or grid_dim-2)
    boundary_cells = sorted([cell for cell in coarse_path_cells if cell[0] == 1 or cell[0] == grid_w - 2 or cell[1] == 1 or cell[1] == grid_h - 2])
    if len(boundary_cells) < 2: # Need at least two points for entrance/exit
        print("Warning: Maze gen - Not enough boundary cells for entrance/exit.", file=sys.stderr)
        # Fallback: return maze without specific openings, player must find way out if needed
        return full_maze_walls, expanded_path, None, None

    # Choose distinct entrance/exit from boundary cells
    entrance_coarse = random.choice(boundary_cells)
    exit_candidates = [cell for cell in boundary_cells if cell != entrance_coarse]
    # Ensure exit is reasonably far from entrance if possible
    max_dist = -1
    best_exit = None
    entrance_x, entrance_y = entrance_coarse
    for cell in exit_candidates:
        dist_sq = (cell[0] - entrance_x)**2 + (cell[1] - entrance_y)**2
        if dist_sq > max_dist:
            max_dist = dist_sq
            best_exit = cell
    exit_coarse = best_exit if best_exit else (random.choice(exit_candidates) if exit_candidates else entrance_coarse) # Fallback needed if only one boundary cell somehow


    # Calculate center coords in full grid for entrance/exit (relative to 0,0)
    entrance_center_x = entrance_coarse[0] * corridor_w + corridor_offset
    entrance_center_y = entrance_coarse[1] * corridor_w + corridor_offset
    exit_center_x = exit_coarse[0] * corridor_w + corridor_offset
    exit_center_y = exit_coarse[1] * corridor_w + corridor_offset

    # Store the relative entrance/exit coords (might be useful later)
    # These are points *inside* the maze path near the opening.
    entrance_coord = (entrance_center_x, entrance_center_y)
    exit_coord = (exit_center_x, exit_center_y)

    # --- MAZE ENTRY FIX (Option A Implementation) ---
    # Carve openings one step *inside* the maze boundary (index 1 or dim-2)
    # This assumes the snake is confined to the 1..(screen_dim-2) playable area
    # and allows the snake to reach the opening.
    # Note: Requires target_h/w to be at least 3. Checked earlier.
    def carve_opening(coarse_cell, center_x, center_y):
        ccw, cch = coarse_cell
        carve_y, carve_x = -1, -1 # Init with invalid values

        if cch == 1: # Top edge -> carve at y=1
            carve_y = 1
            for dx in range(-corridor_offset, corridor_offset + 1):
                 if 0 <= center_x + dx < target_w: full_maze_walls.discard((center_x + dx, carve_y))
        elif cch == grid_h - 2: # Bottom edge -> carve at y=target_h-2
            carve_y = target_h - 2
            for dx in range(-corridor_offset, corridor_offset + 1):
                 if 0 <= center_x + dx < target_w: full_maze_walls.discard((center_x + dx, carve_y))
        elif ccw == 1: # Left edge -> carve at x=1
            carve_x = 1
            for dy in range(-corridor_offset, corridor_offset + 1):
                 if 0 <= center_y + dy < target_h: full_maze_walls.discard((carve_x, center_y + dy))
        elif ccw == grid_w - 2: # Right edge -> carve at x=target_w-2
            carve_x = target_w - 2
            for dy in range(-corridor_offset, corridor_offset + 1):
                 if 0 <= center_y + dy < target_h: full_maze_walls.discard((carve_x, center_y + dy))
        # print(f"Debug: Carved opening for coarse {coarse_cell} at X:{carve_x}, Y:{carve_y}", file=sys.stderr)


    carve_opening(entrance_coarse, entrance_center_x, entrance_center_y)
    carve_opening(exit_coarse, exit_center_x, exit_center_y)


    return full_maze_walls, expanded_path, entrance_coord, exit_coord


# --- Power-up Effect Management ---
def update_active_effects(stdscr, snake, current_timeout, difficulty_timeout):
    """Updates state for active power-ups. Returns new state flags/timeout."""
    global active_effects, ball_powerup_count, score, type1_food_spawn_count
    global last_type1_decrement_time, foods, maze_food_items
    sh, sw = stdscr.getmaxyx(); current_time = time.time()
    new_timeout = current_timeout; expired_indices = []
    is_thick_active = False; active_obstacles = set(); active_maze_walls = set(); is_maze_active = False
    user_head = snake[0] if snake else None

    # Collect maze walls from active maze effects FIRST
    for effect in active_effects:
         if effect['type'] == 8:
             active_maze_walls.update(effect.get('data', {}).get('maze_walls', set()))
             is_maze_active = True # Set flag if any maze effect is active


    if current_time - last_type1_decrement_time > TYPE1_DECREMENT_INTERVAL:
        if type1_food_spawn_count > 1: type1_food_spawn_count -= 1
        last_type1_decrement_time = current_time

    # Process effects and check for expiration
    for i, effect in enumerate(active_effects):
        if current_time >= effect['end_time']:
            if i not in expired_indices: expired_indices.append(i)
            effect_type = effect['type']
             # Restore timeout if effect modified it
            if effect_type in [1, 4, 8] and 'original_timeout' in effect.get('data', {}):
                original_timeout = effect['data']['original_timeout']
                # Restore only if no other effect of the same type is still active AND modifying timeout
                restore = True
                for j, other_effect in enumerate(active_effects):
                    if i != j and other_effect['type'] == effect_type and \
                       current_time < other_effect['end_time'] and \
                       'original_timeout' in other_effect.get('data', {}):
                        restore = False
                        break
                if restore:
                     new_timeout = max(MIN_TIMEOUT, min(MAX_TIMEOUT, original_timeout))

            if effect_type == 8: # Maze cleanup
                maze_food_items.clear(); # Clear specific maze food
                # Don't clear normal food here, handled by activation/expiration maybe?
                # Spawn a new regular food item if snake exists
                if snake:
                    all_items = power_ups_on_screen + foods # Avoid placing on other items
                    # Avoid any remaining maze walls? No, maze is gone.
                    new_food_pos = place_item(stdscr, snake, all_items)
                    if new_food_pos: foods.append(new_food_pos)

            # For Type 2 (Balls), ensure balls are removed if effect expires
            elif effect_type == 2:
                 effect['data']['balls'] = []

            continue # Skip update logic for expired effects

        # Update active effects
        effect_type = effect['type']
        effect_data = effect.get('data', {})
        if effect_type == 1: pass # No continuous update needed
        elif effect_type == 2: # Bouncing Balls
            new_balls = []; balls_data = effect_data.get('balls', [])
            if not balls_data:
                # This should not happen if effect is active, but handle defensively
                if i not in expired_indices: expired_indices.append(i); continue

            for ball in balls_data:
                bx, by = ball['pos']; bdx, bdy = ball['vel']
                n_bx, n_by = bx + bdx, by + bdy

                # Bounce off screen edges (1 to dim-2)
                if n_bx <= 0 or n_bx >= sw - 1: bdx *= -1; n_bx = bx # Reverse direction, stay put this frame
                if n_by <= 0 or n_by >= sh - 1: bdy *= -1; n_by = by

                # Simple collision with maze walls (stop ball) - could bounce instead
                if (n_bx, n_by) in active_maze_walls:
                     # Keep current position, maybe zero velocity or just skip update? Stop for now.
                     n_bx, n_by = bx, by
                     # bdx, bdy = 0, 0 # Optional: stop velocity
                else:
                    # Check collision with player snake AFTER moving
                    if (n_bx, n_by) in snake:
                        if len(snake) > 1: snake.pop(); score = max(0, score + PENALTY_BALL)
                        # Ball could disappear or bounce off snake? Disappears for now.
                        continue # Don't add this ball back

                ball['pos'] = (n_bx, n_by); ball['vel'] = (bdx, bdy)
                new_balls.append(ball)

            effect['data']['balls'] = new_balls
            if not new_balls and ball_powerup_count > 0: # Expire if all balls are gone
                 if i not in expired_indices: expired_indices.append(i)


        elif effect_type == 3: is_thick_active = True # Flag used elsewhere
        elif effect_type == 4: pass # No continuous update needed
        elif effect_type == 5: # Enemy Snake
             if not user_head: continue # Need player snake to exist
             enemy_snake = effect_data.get('snake', [])
             if not enemy_snake:
                 if i not in expired_indices: expired_indices.append(i); continue

             target = effect_data.get('target'); state = effect_data.get('state')
             if not target or not state: # Should not happen if active
                  if i not in expired_indices: expired_indices.append(i); continue

             e_head_x, e_head_y = enemy_snake[0]
             last_pos = enemy_snake[1] if len(enemy_snake) > 1 else None
             moved = False

             # Basic AI: Move towards target, with some randomness
             if state in ['seeking_internal', 'leaving']:
                 ideal_dx, ideal_dy = 0, 0
                 if e_head_x != target[0]: ideal_dx = 1 if target[0] > e_head_x else -1
                 if e_head_y != target[1]: ideal_dy = 1 if target[1] > e_head_y else -1

                 # Prioritize axis with greater distance
                 if ideal_dx != 0 and ideal_dy != 0:
                     if abs(target[0] - e_head_x) > abs(target[1] - e_head_y): ideal_dy = 0
                     else: ideal_dx = 0

                 final_dx, final_dy = ideal_dx, ideal_dy
                 # Add random wobble
                 if random.random() < ENEMY_RANDOM_MOVE_CHANCE:
                     possible_wobbles = []
                     if ideal_dx != 0: possible_wobbles = [(0, 1), (0, -1)] # Wobble perpendicular
                     elif ideal_dy != 0: possible_wobbles = [(1, 0), (-1, 0)]
                     # If no ideal move or wobble failed, choose any direction
                     if not possible_wobbles or (ideal_dx == 0 and ideal_dy == 0) : possible_wobbles = [(0,1),(0,-1),(1,0),(-1,0)]
                     # Ensure wobble doesn't go directly backwards if possible
                     if last_pos:
                          back_dx, back_dy = e_head_x - last_pos[0], e_head_y - last_pos[1]
                          possible_wobbles = [(dx, dy) for dx, dy in possible_wobbles if (dx, dy) != (back_dx, back_dy)]
                          if not possible_wobbles: # If only option is backwards, allow it
                               possible_wobbles = [(back_dx, back_dy)]

                     if possible_wobbles: final_dx, final_dy = random.choice(possible_wobbles)


                 next_e_x, next_e_y = e_head_x + final_dx, e_head_y + final_dy
                 new_e_head = (next_e_x, next_e_y)

                 # --- Enemy Maze Collision Check ---
                 collision_with_maze = new_e_head in active_maze_walls
                 # Prevent moving backwards immediately unless stuck
                 is_reverse_move = new_e_head == last_pos

                 if not collision_with_maze and not is_reverse_move:
                     moved = True
                     enemy_snake.insert(0, new_e_head)
                 elif not collision_with_maze and is_reverse_move and len(enemy_snake) > 1:
                      # Allow reverse only if no other option? Or just stop? Stop for now.
                      moved = False
                 elif collision_with_maze:
                      # Hit a maze wall, don't move. Try alternative? For now, just stop.
                      moved = False
                      # Maybe try the ideal move if the random one failed?
                      if (final_dx, final_dy) != (ideal_dx, ideal_dy):
                           next_e_x, next_e_y = e_head_x + ideal_dx, e_head_y + ideal_dy
                           new_e_head_ideal = (next_e_x, next_e_y)
                           if new_e_head_ideal not in active_maze_walls and new_e_head_ideal != last_pos:
                                moved = True
                                enemy_snake.insert(0, new_e_head_ideal)


                 # State transitions and target updates (unchanged logic)
                 if state == 'seeking_internal':
                     target_reached = (enemy_snake[0] == target if moved else False) # Use actual new head
                     internal_timed_out = (current_time >= effect.get('start_time', 0) + ENEMY_INTERNAL_TIMEOUT)
                     if target_reached or internal_timed_out:
                         effect_data['state'] = 'leaving'; ox, oy = enemy_snake[0] # Current pos
                         # Pick a random off-screen target
                         edge = random.choice(['top', 'bottom', 'left', 'right'])
                         off_dist = 5
                         if edge == 'top': oy = -off_dist
                         elif edge == 'bottom': oy = sh + off_dist
                         elif edge == 'left': ox = -off_dist
                         else: ox = sw + off_dist
                         effect_data['target'] = (ox, oy)

                 elif state == 'leaving':
                      # Check if the enemy head (if it moved) is off-screen
                      current_e_head = enemy_snake[0]
                      is_off_screen = not (0 <= current_e_head[0] < sw and 0 <= current_e_head[1] < sh)
                      if is_off_screen:
                           # Remove the head segment that went off-screen
                           enemy_snake.pop(0)
                           # Continue removing tail segments until none are left or effect expires
                           if len(enemy_snake) > 0: enemy_snake.pop()
                           else: # Snake is fully off-screen
                               if i not in expired_indices: expired_indices.append(i)
                           moved = False # Don't pop tail below if snake emptied

             # Pop tail if enemy moved and didn't grow implicitly
             if moved:
                 # Check if enemy grew (e.g. maybe from hitting player in future?) - for now, always pop
                 if len(enemy_snake) > 1 : # Only pop if there's a tail
                      enemy_snake.pop()
             elif not moved and state != 'leaving': # Didn't move, shrink if not leaving
                  if len(enemy_snake) > 1: enemy_snake.pop()


             # Check if enemy snake still exists
             if not enemy_snake:
                 if i not in expired_indices: expired_indices.append(i); continue

             effect['data']['snake'] = enemy_snake # Update effect data

             # --- Player vs Enemy Collision ---
             # Check after enemy potentially moved
             if user_head and enemy_snake: # Check if player and enemy still exist
                 enemy_head = enemy_snake[0]
                 if user_head == enemy_head: # Head-on collision
                     # Player absorbs enemy
                     segments_to_add = list(reversed(enemy_snake[1:]))
                     if segments_to_add: snake.extend(segments_to_add)
                     score += SCORE_ENEMY_HEAD
                     # Remove the enemy effect
                     if i not in expired_indices: expired_indices.append(i);
                     # Trigger growth flag? No, handled by extend.
                 elif user_head in enemy_snake[1:]: # Player hits enemy body
                     if len(snake) > 1:
                         segments_to_remove = max(1, len(snake) // 3) # Penalty
                         score = max(0, score + PENALTY_ENEMY_BODY)
                         for _ in range(segments_to_remove):
                             if len(snake) > 1: snake.pop()
                             else: break # Don't remove the head
                     elif len(snake) == 1: # Kill player if only head remains
                          snake.clear() # Signal game over
                     # Enemy snake might split here in future, but not implemented currently


        elif effect_type == 6: active_obstacles.update(effect_data.get('blocks', [])) # Used for collision checks elsewhere
        elif effect_type == 7: # Meteor Rain
            new_meteors = []; meteors_data = effect_data.get('meteors', [])
            if not meteors_data:
                 if i not in expired_indices: expired_indices.append(i); continue

            for meteor in meteors_data:
                mx, my = meteor['pos']; mdx, mdy = meteor['vel']
                nmy = my + mdy; nmx = mx + mdx

                # Check screen bounds first
                if not (0 <= nmx < sw): continue # Disappears if goes off sides

                next_pos = (nmx, nmy)

                # --- Meteor Maze Collision Check ---
                if next_pos in active_maze_walls:
                    # Meteor hits wall, disappears
                    continue # Don't add back to list

                meteor['pos'] = next_pos # Update position

                # Check collision with player snake
                if meteor['pos'] in snake:
                    if len(snake) > 1: snake.pop(); score = max(0, score + PENALTY_METEOR)
                    # Meteor disappears after hitting snake
                    continue # Don't add back to list

                # Keep meteor if still on screen vertically
                if nmy < sh:
                    new_meteors.append(meteor)

            effect['data']['meteors'] = new_meteors
            if not new_meteors: # Expire if all meteors are gone
                 if i not in expired_indices: expired_indices.append(i)


        elif effect_type == 8:
            # Maze walls collected earlier, no continuous update needed for walls themselves
            pass # is_maze_active flag is set based on presence


    # --- Cleanup Expired Effects ---
    if expired_indices:
        expired_indices.sort(reverse=True) # Sort to delete from end without index issues
        for i in expired_indices:
            if 0 <= i < len(active_effects):
                # print(f"Debug: Removing effect type {active_effects[i]['type']} at index {i}", file=sys.stderr)
                del active_effects[i]

    # --- Recalculate State Flags After Cleanup ---
    is_any_effect_active = len(active_effects) > 0
    is_thick_active = any(eff['type'] == 3 for eff in active_effects)
    # is_maze_active is already updated based on initial loop
    # recalculate active_obstacles and active_maze_walls based on remaining effects
    active_obstacles = set().union(*(eff['data'].get('blocks', set()) for eff in active_effects if eff['type'] == 6))
    active_maze_walls = set().union(*(eff['data'].get('maze_walls', set()) for eff in active_effects if eff['type'] == 8))
    is_maze_active = len(active_maze_walls) > 0


    # Ensure timeout is within bounds
    new_timeout = max(MIN_TIMEOUT, min(MAX_TIMEOUT, new_timeout))

    return new_timeout, is_any_effect_active, is_thick_active, active_obstacles, active_maze_walls, is_maze_active

def draw_active_effects(stdscr, has_colors):
    """Draws visuals for active effects (balls, enemy, obstacles, meteors, maze)."""
    global active_effects, maze_food_items
    sh, sw = stdscr.getmaxyx()
    obstacle_attrib = curses.color_pair(OBSTACLE_PAIR) if has_colors else 0
    meteor_attrib = curses.color_pair(METEOR_PAIR) if has_colors else 0
    maze_wall_attrib = curses.color_pair(MAZE_WALL_PAIR) if has_colors else 0
    maze_food_attrib = curses.color_pair(MAZE_FOOD_PAIR) if has_colors else 0
    ball_attrib = curses.color_pair(BALL_PAIR) if has_colors else 0
    enemy_attrib = curses.color_pair(ENEMY_SNAKE_PAIR) if has_colors else 0

    # Draw maze walls and food first (static background elements)
    maze_walls_drawn = set()
    maze_food_drawn = set()
    for effect in active_effects:
         if effect['type'] == 8:
            # Draw Maze Walls using 'maze_walls' key from effect data
            for wx, wy in effect.get('data',{}).get('maze_walls', []): # Use the walls from effect data
                if (wx, wy) not in maze_walls_drawn: # Avoid overdrawing if multiple effects somehow
                    if 0 <= wy < sh and 0 <= wx < sw:
                        try: stdscr.addch(wy, wx, WALL_SYMBOL, maze_wall_attrib)
                        except curses.error: pass # Ignore drawing errors at edge
                    maze_walls_drawn.add((wx, wy))

    # Draw Maze Food using global list (populated during activation)
    for fx, fy in maze_food_items:
        if (fx, fy) not in maze_food_drawn:
             if 0 <= fy < sh and 0 <= fx < sw:
                try: stdscr.addch(fy, fx, FOOD_SYMBOL, maze_food_attrib)
                except curses.error: pass
             maze_food_drawn.add((fx,fy))

    # Draw other dynamic elements
    for effect in active_effects:
        effect_type = effect['type']; effect_data = effect.get('data', {})
        if effect_type == 2: # Balls
            for ball in effect_data.get('balls', []):
                bx, by = ball['pos'];
                if 0 <= by < sh and 0 <= bx < sw:
                    # Avoid drawing over maze walls (optional, makes walls solid)
                    # if (bx, by) not in maze_walls_drawn:
                        try: stdscr.addch(by, bx, BALL_SYMBOL, ball_attrib)
                        except curses.error: pass
        elif effect_type == 5: # Enemy Snake
            for seg in effect_data.get('snake', []):
                ex, ey = seg;
                if 0 <= ey < sh and 0 <= ex < sw:
                     # Avoid drawing over maze walls? Or let enemy phase through? Let it phase for now.
                     # if (ex, ey) not in maze_walls_drawn:
                        try: stdscr.addch(ey, ex, ENEMY_SNAKE_SYMBOL, enemy_attrib)
                        except curses.error: pass
        elif effect_type == 6: # Obstacles
            for ox, oy in effect_data.get('blocks', []):
                 # Avoid drawing over maze walls? Obstacles likely permanent. Let them draw over.
                 if 0 <= oy < sh and 0 <= ox < sw:
                    try: stdscr.addch(oy, ox, OBSTACLE_SYMBOL, obstacle_attrib)
                    except curses.error: pass
        elif effect_type == 7: # Meteors
            for meteor in effect_data.get('meteors', []):
                mx, my = meteor['pos']
                if 0 <= my < sh and 0 <= mx < sw:
                     # Avoid drawing over maze walls? Let them phase.
                     # if (mx, my) not in maze_walls_drawn:
                        try: stdscr.addch(my, mx, METEOR_SYMBOL, meteor_attrib)
                        except curses.error: pass
        # Type 8 (Maze) walls/food drawn already

# --- Power-up Activation Logic ---
def activate_powerup(ptype, current_loop_time, stdscr, snake, current_timeout,
                     base_difficulty_timeout, powerup_slowdown_factor, difficulty_key, has_colors):
    """Handles activation logic. Returns new timeout. Sets flash message."""
    global active_effects, score, type1_food_spawn_count, ball_powerup_count
    global maze_food_items, foods, power_ups_on_screen
    global flash_message, flash_message_end_time
    global maze_just_activated # Import the global flag

    # Ensure snake exists to base length on or activate powerup
    # Check specifically needed for Type 5 variant B
    if not snake and ptype == 5: # Cannot activate dynamic length enemy if snake doesn't exist
        print("Warning: Cannot activate Type 5 (Dynamic Length) enemy - player snake is empty.", file=sys.stderr)
        return current_timeout
    elif not snake and ptype != 5: # General check for other types
        return current_timeout


    sh, sw = stdscr.getmaxyx()

    # Determine duration (remains the same for Type 5)
    effect_duration = 0
    if ptype == 8: # Maze duration from difficulty
        if isinstance(POWERUP_DURATIONS[8], dict): effect_duration = POWERUP_DURATIONS[8].get(difficulty_key, 45)
        else: print("Warning: POWERUP_DURATIONS[8] structure error", file=sys.stderr); effect_duration = 45
    elif ptype in POWERUP_DURATIONS:
        duration_source = POWERUP_DURATIONS[ptype]
        effect_duration = duration_source() if callable(duration_source) else duration_source
    else:
         print(f"Error: Duration missing for powerup {ptype}", file=sys.stderr); return current_timeout

    effect_end_time = current_loop_time + effect_duration
    new_effect = {'type': ptype, 'end_time': effect_end_time, 'data': {}, 'start_time': current_loop_time}
    activation_successful = True # Assume success unless specific logic fails

    # --- Specific Activation Logic ---
    # (Types 1, 2, 3, 4, 6, 7, 8 remain unchanged from previous version)
    if ptype == 1: # Multi-Food & Slowdown
        type1_food_spawn_count += 1
        new_effect['data']['original_timeout'] = current_timeout # Store timeout to restore later
        timeout_increase = int(current_timeout * powerup_slowdown_factor)
        current_timeout = min(MAX_TIMEOUT, current_timeout + timeout_increase)
        stdscr.timeout(current_timeout) # Apply slowdown

        foods.clear() # Clear existing regular food
        all_items_to_avoid = list(snake) + power_ups_on_screen
        all_items_to_avoid.extend(list(set().union(*(eff['data'].get('blocks', set()) for eff in active_effects if eff['type'] == 6)))) # Obstacles
        all_items_to_avoid.extend(list(set().union(*(eff['data'].get('maze_walls', set()) for eff in active_effects if eff['type'] == 8)))) # Maze Walls

        spawned_count = 0
        for _ in range(type1_food_spawn_count):
            new_food_pos = place_item(stdscr, snake, all_items_to_avoid)
            if new_food_pos:
                foods.append(new_food_pos)
                all_items_to_avoid.append(new_food_pos)
                spawned_count += 1
            else: break
        if spawned_count == 0 and type1_food_spawn_count > 0:
            print("Warning: No food spawned for Type 1 activation.", file=sys.stderr)

    elif ptype == 2: # Bouncing Balls
        ball_powerup_count += 1
        new_effect['data']['balls'] = []
        all_items_to_avoid = list(snake) + foods + power_ups_on_screen
        all_items_to_avoid.extend(list(set().union(*(eff['data'].get('blocks', set()) for eff in active_effects if eff['type'] == 6)))) # Obstacles
        all_items_to_avoid.extend(list(set().union(*(eff['data'].get('maze_walls', set()) for eff in active_effects if eff['type'] == 8)))) # Maze Walls
        for eff in active_effects:
             if eff['type'] == 2: all_items_to_avoid.extend([b['pos'] for b in eff['data'].get('balls',[])])

        spawned_count = 0
        for _ in range(ball_powerup_count): # Spawn cumulative number of balls
            ball_start_pos = place_item(stdscr, snake, all_items_to_avoid)
            if ball_start_pos:
                ball_vel = random.choice([(1,1), (1,-1), (-1,1), (-1,-1)])
                new_effect['data']['balls'].append({'pos': ball_start_pos, 'vel': ball_vel})
                all_items_to_avoid.append({'pos': ball_start_pos})
                spawned_count += 1
            else: break
        if spawned_count == 0 and ball_powerup_count > 0:
            print("Warning: No balls spawned for Type 2 activation.", file=sys.stderr)
            activation_successful = False

    elif ptype == 3: # Thick Snake
        pass

    elif ptype == 4: # MAX SPEED
        new_effect['data']['original_timeout'] = current_timeout
        current_timeout = MIN_TIMEOUT
        stdscr.timeout(current_timeout)

    # --- MODIFIED ENEMY SNAKE LOGIC ---
    elif ptype == 5: # Enemy Snake (Two Types)
        player_length = len(snake) # Get current player length

        # Randomly choose enemy type
        is_long_type = random.random() < 0.5 # 50% chance for long type

        if is_long_type:
            target_length = 100
            enemy_type_name = "Long Fixed (100)"
        else:
            target_length = max(3, player_length * 2) # Double player length, minimum 3
            enemy_type_name = f"Dynamic ({target_length})"

        print(f"Activating Enemy Snake - Type: {enemy_type_name}", file=sys.stderr)

        # Determine starting edge and head position (sx, sy) - Same as before
        start_edge = random.choice(['top', 'bottom', 'left', 'right'])
        sx, sy = 0, 0
        tail_dx, tail_dy = 0, 0 # Direction the tail extends *away* from screen

        if start_edge == 'top':
            sx = random.randint(1, sw - 2); sy = 0
            tail_dx, tail_dy = 0, -1 # Tail goes up (negative y)
        elif start_edge == 'bottom':
            sx = random.randint(1, sw - 2); sy = sh - 1
            tail_dx, tail_dy = 0, 1 # Tail goes down (positive y)
        elif start_edge == 'left':
            sx = 0; sy = random.randint(1, sh - 2)
            tail_dx, tail_dy = -1, 0 # Tail goes left (negative x)
        else: # right
            sx = sw - 1; sy = random.randint(1, sh - 2)
            tail_dx, tail_dy = 1, 0 # Tail goes right (positive x)

        # Generate the initial segments, starting with head, extending off-screen
        enemy_segments = [(sx, sy)] # Start with the head segment
        last_seg_x, last_seg_y = sx, sy
        for _ in range(target_length - 1):
            next_seg_x = last_seg_x + tail_dx
            next_seg_y = last_seg_y + tail_dy
            enemy_segments.append((next_seg_x, next_seg_y))
            last_seg_x, last_seg_y = next_seg_x, next_seg_y

        # Determine internal target position (ix, iy) - Same as before
        ix, iy = random.randint(sw//4, 3*sw//4), random.randint(sh//4, 3*sh//4)

        # Initial state for the new enemy - now with the full segment list
        new_effect['data'] = {
            'snake': enemy_segments, # List of segments
            'target': (ix, iy),
            'state': 'seeking_internal',
            'enemy_type': enemy_type_name # Optional: store type if needed later
            }
    # --- END OF MODIFIED ENEMY SNAKE LOGIC ---

    elif ptype == 6: # Obstacle Blocks
        num_obstacles = max(1, len(snake) // 2)
        placed_obstacles = []
        all_items_to_avoid = list(snake) + foods + power_ups_on_screen
        current_obstacles_coords = set().union(*(eff['data'].get('blocks', set()) for eff in active_effects if eff['type'] == 6))
        all_items_to_avoid.extend(list(current_obstacles_coords))
        all_items_to_avoid.extend(list(set().union(*(eff['data'].get('maze_walls', set()) for eff in active_effects if eff['type'] == 8))))

        for _ in range(num_obstacles):
            pos = place_item(stdscr, snake, all_items_to_avoid, max_attempts=MAX_OBSTACLE_PLACEMENT_ATTEMPTS)
            if pos:
                placed_obstacles.append(pos)
                all_items_to_avoid.append(pos)
            else:
                print(f"Warning: Placed {len(placed_obstacles)}/{num_obstacles} obstacles. No more space?", file=sys.stderr)
                break

        min_required_obstacles = max(1, num_obstacles // 2) if num_obstacles > 0 else 0
        if num_obstacles > 0 and len(placed_obstacles) < min_required_obstacles:
            score = max(0, score + PENALTY_OBSTACLE_FAIL)
            if len(snake) > 1:
                segments_to_remove = max(1, len(snake) // 4)
                for _ in range(segments_to_remove):
                    if len(snake) > 1: snake.pop()
                    else: break
            activation_successful = False
            flash_message = "Obstacle Fail! Penalty!"
            flash_message_end_time = current_loop_time + FLASH_MESSAGE_DURATION
            print(f"Obstacle placement failed ({len(placed_obstacles)}/{num_obstacles}), penalty applied.", file=sys.stderr)
        elif placed_obstacles:
            new_effect['data']['blocks'] = set(placed_obstacles)
        else:
            activation_successful = False

    elif ptype == 7: # Meteor Rain
        num_meteors = random.randint(max(1, sw // 15), max(3, sw // 10))
        new_effect['data']['meteors'] = []
        for _ in range(num_meteors):
            m_start_x = random.randint(1, sw - 2)
            m_dx = random.choice([-1, 0, 0, 1])
            new_effect['data']['meteors'].append({'pos': (m_start_x, 0), 'vel': (m_dx, 1)})

    elif ptype == 8: # Wide Maze
        max_maze_cells = int((sh - 2) * (sw - 2) * MAZE_AREA_PERCENTAGE)
        if max_maze_cells < MAZE_CORRIDOR_WIDTH * MAZE_CORRIDOR_WIDTH * 9:
             print(f"Warning: Screen too small ({sh}x{sw}) for minimum maze size.", file=sys.stderr)
             activation_successful = False
             flash_message = "Maze Failed (Screen Size?)"
             flash_message_end_time = current_loop_time + FLASH_MESSAGE_DURATION
        else:
            aspect_ratio = (sw - 2) / (sh - 2) if sh > 2 else 1.0
            approx_h = int(math.sqrt(max_maze_cells / aspect_ratio))
            approx_w = int(aspect_ratio * approx_h)
            target_h = min(sh - 2, max(MAZE_CORRIDOR_WIDTH * 3, approx_h))
            target_w = min(sw - 2, max(MAZE_CORRIDOR_WIDTH * 3, approx_w))
            offset_y = max(1, (sh - target_h) // 2)
            offset_x = max(1, (sw - target_w) // 2)

            rel_maze_walls, rel_expanded_path, rel_entrance, rel_exit = \
                generate_wide_maze(target_h, target_w, MAZE_CORRIDOR_WIDTH)

            if rel_expanded_path:
                offset_maze_walls = set((cx + offset_x, cy + offset_y) for cx, cy in rel_maze_walls)
                offset_expanded_path = set((cx + offset_x, cy + offset_y) for cx, cy in rel_expanded_path)
                offset_entrance = (rel_entrance[0] + offset_x, rel_entrance[1] + offset_y) if rel_entrance else None
                offset_exit = (rel_exit[0] + offset_x, rel_exit[1] + offset_y) if rel_exit else None

                head_pos = snake[0]
                if head_pos in offset_maze_walls:
                    offset_maze_walls.discard(head_pos)
                    print(f"Note: Cleared maze wall at snake start pos {head_pos}", file=sys.stderr)

                new_effect['data']['original_timeout'] = current_timeout
                current_timeout = min(MAX_TIMEOUT, int(current_timeout * MAZE_SLOWDOWN_FACTOR))
                stdscr.timeout(current_timeout)

                items_to_avoid_maze_food = list(snake) + power_ups_on_screen
                available_offset_path_list = list(offset_expanded_path - set(items_to_avoid_maze_food))
                maze_food_items.clear()

                if not available_offset_path_list:
                    print("Warning: Maze generated, but no valid path cells for food.", file=sys.stderr)
                else:
                    num_path_cells = len(available_offset_path_list)
                    num_maze_food = max(1, num_path_cells // MAZE_FOOD_DENSITY)
                    num_maze_food = min(num_maze_food, num_path_cells)
                    try:
                        maze_food_coords_offset = random.sample(available_offset_path_list, num_maze_food)
                        maze_food_items.extend(maze_food_coords_offset)
                    except ValueError as e:
                         print(f"Error sampling maze food positions: {e}", file=sys.stderr)

                new_effect['data']['maze_walls'] = offset_maze_walls
                new_effect['data']['maze_entrance'] = offset_entrance
                new_effect['data']['maze_exit'] = offset_exit
                foods.clear()
                maze_just_activated = True
            else:
                activation_successful = False
                flash_message = "Maze Failed (Generation Error)"
                flash_message_end_time = current_loop_time + FLASH_MESSAGE_DURATION
                print("Error: Wide maze generation failed.", file=sys.stderr)


    # --- Finalize Activation ---
    if activation_successful:
        active_effects.append(new_effect)
        if not flash_message: # Don't overwrite failure messages
             flash_message = POWERUP_NAMES.get(ptype, f"Power Up Type {ptype}!")
             # Use shorter duration for enemy spawn message?
             msg_duration = FLASH_MESSAGE_DURATION
             if ptype == 5: msg_duration = 1.5 # Shorter message for enemy type
             flash_message_end_time = current_loop_time + msg_duration

    else: # Activation failed or was cancelled
         if ptype == 8: maze_just_activated = False
         if ptype in [1, 4, 8] and 'original_timeout' in new_effect['data']:
              current_timeout = new_effect['data']['original_timeout']
              stdscr.timeout(current_timeout)
         print(f"Powerup type {ptype} activation cancelled or failed.", file=sys.stderr)
         # Clear any potentially set flash message if activation failed here
         if flash_message and flash_message_end_time == current_loop_time + FLASH_MESSAGE_DURATION:
              flash_message = None


    return current_timeout # Return potentially modified timeout


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
    global maze_just_activated # Need global scope for the freeze flag

    # --- Initial Setup ---
    curses.curs_set(0); stdscr.nodelay(True); stdscr.keypad(True)
    sh, sw = stdscr.getmaxyx()
    min_h, min_w = 15, 40 # Adjusted minimum slightly, maze needs some space
    if sh < min_h or sw < min_w:
        try: curses.endwin()
        except: pass
        print(f"Terminal too small (Min: {min_w}x{min_h}, Has: {sw}x{sh})")
        print("Maze generation requires roughly 15x40 minimum.")
        return

    has_colors = init_colors()
    flash_message_attrib = curses.color_pair(SNAKE_FLASH_PAIR) | curses.A_BOLD if has_colors else curses.A_BOLD
    maze_snake_attrib = curses.color_pair(MAZE_SNAKE_PAIR) | curses.A_BOLD if has_colors else curses.A_BOLD

    # --- Difficulty Selection ---
    difficulty, difficulty_key = select_difficulty(stdscr, has_colors)
    if difficulty is None: return # User chose 'q'

    base_difficulty_timeout = difficulty["timeout"]
    speed_increase_factor = difficulty["increase"] / 100.0
    powerup_slowdown_factor = difficulty["slowdown"] / 100.0

    # --- Outer Game Loop (Allows Replay) ---
    play_again = True
    while play_again:

        reset_game_state() # Reset globals for a fresh game
        current_timeout = base_difficulty_timeout
        stdscr.timeout(current_timeout)

        # Initial snake setup
        start_x, start_y = sw // 4, sh // 2
        snake = [(start_x, start_y), (start_x - 1, start_y), (start_x - 2, start_y)]
        direction = curses.KEY_RIGHT

        # Initial food placement
        initial_food_pos = place_item(stdscr, snake, [])
        if initial_food_pos: foods.append(initial_food_pos)
        else: print("Warning: Could not place initial food. Terminal might be too small.", file=sys.stderr)

        # Power-up timing
        next_power_up_spawn_time = time.time() + random.uniform(15, 45) # Spawn first one a bit sooner

        # --- Test Mode Activation ---
        if test_mode:
            print("--- TEST MODE: Activating all powerups ---", file=sys.stderr)
            current_activate_time = time.time()
            test_mode_maze_activated = False # Track if maze activated in test
            for ptype_test in sorted(POWERUP_TYPES):
                print(f"Activating test powerup: {POWERUP_NAMES.get(ptype_test, ptype_test)} ({ptype_test})", file=sys.stderr)
                # Store current state before activation
                was_active = any(e['type'] == ptype_test for e in active_effects)
                prev_timeout = current_timeout
                prev_maze_just_activated = maze_just_activated

                current_timeout = activate_powerup(
                    ptype_test, current_activate_time, stdscr, snake,
                    current_timeout, base_difficulty_timeout, powerup_slowdown_factor,
                    difficulty_key, has_colors
                )
                stdscr.timeout(current_timeout) # Ensure timeout is updated immediately

                # Check if activation was successful and if it was maze type 8
                is_now_active = any(e['type'] == ptype_test for e in active_effects)
                powerup_actually_activated = is_now_active and (not was_active or ptype_test in [1, 2]) # Types 1,2 stack
                maze_triggered_this_activation = (ptype_test == 8 and maze_just_activated and not prev_maze_just_activated)

                if maze_triggered_this_activation:
                     test_mode_maze_activated = True # Set flag for freeze after loop

                print(f"  -> Activated: {powerup_actually_activated}, Timeout: {current_timeout}, Maze Freeze Triggered: {maze_triggered_this_activation}", file=sys.stderr)
                # Need to reset maze_just_activated if it was set, so next iteration doesn't reuse it
                if maze_triggered_this_activation: maze_just_activated = False


            # Handle freeze after all activations if maze was triggered during the test loop
            if test_mode_maze_activated:
                print(f"Test Mode: Freezing for {MAZE_INITIAL_FREEZE_S}s after activations...", file=sys.stderr)
                # Perform a draw before sleeping to show the initial state
                stdscr.clear()
                # Draw relevant elements: snake, effects (including maze), maybe status
                status_line = f"Score: {score} | Speed: {current_timeout}ms | Len: {len(snake)}"
                try: stdscr.addstr(0, 1, status_line[:sw-1])
                except curses.error: pass
                draw_active_effects(stdscr, has_colors) # Draw maze walls/food etc.
                if snake: # Draw snake
                     snake_attrib = curses.color_pair(MAZE_SNAKE_PAIR) if has_colors else 0
                     for seg_x, seg_y in snake:
                          if 0 <= seg_y < sh and 0 <= seg_x < sw:
                              try: stdscr.addch(seg_y, seg_x, SNAKE_SYMBOL, snake_attrib)
                              except curses.error: pass

                stdscr.refresh()
                time.sleep(MAZE_INITIAL_FREEZE_S)
                curses.flushinp() # Clear any input buffer during freeze
                print("--- Test mode freeze complete ---", file=sys.stderr)
            else:
                 print("--- Test mode activation complete (No maze freeze) ---", file=sys.stderr)


        # --- Inner Game Loop ---
        game_over = False; quit_game = False
        while not game_over and not quit_game:
            current_loop_time = time.time()
            grew_from_eating = False # Reset growth flag each tick

            # Handle Maze Initial Freeze (set during activation)
            if maze_just_activated:
                # Need to draw the state *before* sleeping
                stdscr.clear()
                # Status Line
                status_line = f"Score: {score} | Speed: {current_timeout}ms | Len: {len(snake)}"
                try: stdscr.addstr(0, 1, status_line[:sw-1])
                except curses.error: pass
                # Draw maze walls/food etc.
                draw_active_effects(stdscr, has_colors)
                 # Draw snake (should be yellow now)
                if snake:
                    snake_attrib = curses.color_pair(MAZE_SNAKE_PAIR)|curses.A_BOLD if has_colors else curses.A_BOLD
                    for seg_x, seg_y in snake:
                        if 0 <= seg_y < sh and 0 <= seg_x < sw:
                            try: stdscr.addch(seg_y, seg_x, SNAKE_SYMBOL, snake_attrib)
                            except curses.error: pass
                stdscr.refresh()

                time.sleep(MAZE_INITIAL_FREEZE_S)
                curses.flushinp() # Clear input buffer
                maze_just_activated = False # Reset flag


            # 1. Input Handling
            key = stdscr.getch(); new_direction = direction
            valid_key_pressed = False
            if key == curses.KEY_LEFT and direction != curses.KEY_RIGHT: new_direction = curses.KEY_LEFT; valid_key_pressed = True
            elif key == curses.KEY_RIGHT and direction != curses.KEY_LEFT: new_direction = curses.KEY_RIGHT; valid_key_pressed = True
            elif key == curses.KEY_UP and direction != curses.KEY_DOWN: new_direction = curses.KEY_UP; valid_key_pressed = True
            elif key == curses.KEY_DOWN and direction != curses.KEY_UP: new_direction = curses.KEY_DOWN; valid_key_pressed = True
            elif key == ord('q'): quit_game = True; continue
            elif key == ord('p'): # Pause functionality
                 stdscr.nodelay(False) # Turn off non-blocking input
                 pause_msg = "Paused - Press 'p' to resume"
                 msg_y = sh // 2; msg_x = sw // 2 - len(pause_msg)//2
                 stdscr.addstr(msg_y, msg_x, pause_msg, curses.A_BOLD)
                 stdscr.refresh()
                 while stdscr.getch() != ord('p'): pass
                 stdscr.nodelay(True) # Turn back on non-blocking
                 curses.flushinp() # Clear buffer after pause

            # Secret code handling ('xxx' to trigger maze)
            elif key == ord('x'): key_press_history.append('x')
            elif key != -1: key_press_history.clear() # Clear history on any other key press

            if valid_key_pressed: direction = new_direction

            # 2. Secret Code Activation ('xxx')
            is_maze_already_active_check = any(eff['type'] == 8 for eff in active_effects)
            if list(key_press_history) == ['x', 'x', 'x'] and not is_maze_already_active_check:
                # Temporarily store current state flags that activate_powerup might change
                was_maze_just_activated = maze_just_activated

                current_timeout = activate_powerup(8, current_loop_time, stdscr, snake, current_timeout, base_difficulty_timeout, powerup_slowdown_factor, difficulty_key, has_colors)

                # maze_just_activated flag is set inside activate_powerup if successful
                stdscr.timeout(current_timeout)
                key_press_history.clear()


            # 3. Update Active Power-up Effects & Get Current State
            # This updates positions, checks expirations, handles collisions internal to effects
            current_timeout, is_any_effect_active, is_thick_active, \
            active_obstacles, active_maze_walls, is_maze_active = \
                update_active_effects(stdscr, snake, current_timeout, base_difficulty_timeout)
            stdscr.timeout(current_timeout) # Apply timeout changes from effects

            # 4. Check for Game Over from Effects (e.g., snake shrunk to nothing)
            if not snake: game_over = True; continue

            # 5. Snake Visuals (Flashing / Maze Color Override)
            snake_attrib = 0
            if has_colors:
                if is_maze_active: # Maze takes priority
                    snake_attrib = maze_snake_attrib
                elif is_any_effect_active: # Flash if any other effect active
                    if current_loop_time - last_flash_time > FLASH_INTERVAL:
                         flash_on = not flash_on; last_flash_time = current_loop_time
                    snake_attrib = curses.color_pair(SNAKE_FLASH_PAIR if flash_on else DEFAULT_PAIR)
                else: # Default color
                    snake_attrib = curses.color_pair(DEFAULT_PAIR); flash_on = False # Ensure flash stops
            else: # No colors
                 snake_attrib = 0


            # 6. Calculate Snake's Next Head Position
            # Need snake check again, as update_effects might have killed it
            if not snake: game_over = True; continue
            head_x, head_y = snake[0]
            next_head_x, next_head_y = head_x, head_y # Start with current head

            if direction == curses.KEY_RIGHT: next_head_x += 1
            elif direction == curses.KEY_LEFT: next_head_x -= 1
            elif direction == curses.KEY_UP: next_head_y -= 1
            elif direction == curses.KEY_DOWN: next_head_y += 1

            new_head = (next_head_x, next_head_y)

            # 7. Check Collisions (Wall, Self, Obstacles, Maze Walls)
            # --- IMPORTANT: Check collisions BEFORE moving snake ---
            # Check screen boundary collision
            # Note: Maze openings are now at 1/dim-2, so hitting 0/dim-1 is always game over
            wall_hit = next_head_x < 0 or next_head_x >= sw or next_head_y < 0 or next_head_y >= sh

            # Check self collision (new head position against existing body)
            # Need slicing snake[1:] if thick snake extra part can overlap tail
            self_collision = len(snake) > 1 and new_head in snake # Check against entire snake before move

            # Check collision with active obstacles
            obstacle_hit = new_head in active_obstacles

            # Check collision with active maze walls
            # active_maze_walls is updated in update_active_effects
            maze_wall_hit = new_head in active_maze_walls

            if wall_hit or self_collision or obstacle_hit or maze_wall_hit:
                # Optional: Identify cause for debug/message
                # cause = "Wall" if wall_hit else "Self" if self_collision else "Obstacle" if obstacle_hit else "Maze Wall"
                # print(f"Game Over: Collision detected - {cause} at {new_head}", file=sys.stderr)
                game_over = True; continue # Skip movement and drawing for this frame


            # 8. Move Snake (Add new head)
            snake.insert(0, new_head)

            # 9. Food Consumption (Regular and Maze Food)
            consumed_food_pos = None
            food_score_increase = 0
            is_maze_food_consumed = False

            # Determine which food list to check
            food_list_to_check = maze_food_items if is_maze_active else foods
            food_score_value = SCORE_MAZE_FOOD if is_maze_active else SCORE_FOOD

            # Check head collision with food
            food_to_remove_index = -1
            for i, food_pos in enumerate(food_list_to_check):
                if new_head == food_pos:
                    consumed_food_pos = food_pos
                    food_score_increase = food_score_value
                    is_maze_food_consumed = is_maze_active
                    food_to_remove_index = i
                    break

            # --- Thick Snake Food Collision Check ---
            if not consumed_food_pos and is_thick_active and len(snake) > 1:
                 # Calculate the adjacent thick segment position based on drawing logic
                 # We need the vector from the *new* second segment (snake[1]) to the head (snake[0])
                 seg1_x, seg1_y = snake[1] # Segment right behind the head
                 head_x, head_y = snake[0] # The new head position
                 dx = head_x - seg1_x
                 dy = head_y - seg1_y
                 adj_x, adj_y = head_x, head_y # Start at head position

                 # Determine the perpendicular adjacent cell based on movement direction
                 if dx != 0: # Moved horizontally
                     adj_y += 1 # Check cell below (or could be above, or both?) Let's stick to one for now.
                 elif dy != 0: # Moved vertically
                     adj_x += 1 # Check cell to the right

                 adj_pos = (adj_x, adj_y)

                 # Check if this adjacent position hits food
                 for i, food_pos in enumerate(food_list_to_check):
                      if adj_pos == food_pos:
                           consumed_food_pos = food_pos
                           food_score_increase = food_score_value
                           is_maze_food_consumed = is_maze_active
                           food_to_remove_index = i
                           print(f"Debug: Thick snake ate food at {food_pos} via segment {adj_pos}", file=sys.stderr)
                           break


            # Process food consumption if any occurred
            if consumed_food_pos is not None:
                grew_from_eating = True
                score += food_score_increase

                # Remove the eaten food
                if food_to_remove_index != -1:
                    del food_list_to_check[food_to_remove_index]

                # Speed up only if it was REGULAR food (not maze food)
                if not is_maze_food_consumed:
                    timeout_reduction = int(current_timeout * speed_increase_factor)
                    current_timeout = max(MIN_TIMEOUT, current_timeout - timeout_reduction)
                    stdscr.timeout(current_timeout)
                    # Spawn new *regular* food
                    all_items_on_screen = foods + power_ups_on_screen + list(active_obstacles) + maze_food_items + list(active_maze_walls)
                    new_food_pos = place_item(stdscr, snake, all_items_on_screen)
                    if new_food_pos: foods.append(new_food_pos)
                    else: print("Warning: Could not place new regular food after eating.", file=sys.stderr)
                # else: No speed up for maze food, and don't spawn new maze food here (handled by initial spawn)


            # 10. Power-up Consumption
            consumed_powerup_type = -1
            if not grew_from_eating and not is_maze_active: # Can only eat powerups if not in maze and didn't just eat food
                powerup_to_remove_index = -1
                for i, (px, py, ptype) in enumerate(power_ups_on_screen):
                    if new_head == (px, py):
                        grew_from_eating = True # Consuming powerup counts as growing (prevents tail pop)
                        powerup_to_remove_index = i
                        consumed_powerup_type = ptype
                        score += SCORE_POWERUP
                        break
                     # Check thick snake collision? Maybe not for powerups. Let's skip for now.

                if consumed_powerup_type != -1:
                    del power_ups_on_screen[powerup_to_remove_index]
                    # Activate the consumed powerup
                    # Need to track if maze was just activated for the freeze
                    prev_maze_just_activated = maze_just_activated
                    current_timeout = activate_powerup(
                        consumed_powerup_type, current_loop_time, stdscr, snake,
                        current_timeout, base_difficulty_timeout, powerup_slowdown_factor,
                        difficulty_key, has_colors
                    )
                    # maze_just_activated flag is set inside activate_powerup
                    stdscr.timeout(current_timeout)


            # 11. Pop Tail if snake didn't grow/eat
            if not grew_from_eating:
                if len(snake) > 0: snake.pop() # Remove last segment

            # Final check: if snake somehow became empty after popping tail
            if not snake: game_over = True; continue

            # 12. Power-up Spawning
            if not is_maze_active and current_loop_time >= next_power_up_spawn_time:
                max_powerups = 5 # Limit number on screen
                if len(power_ups_on_screen) < max_powerups:
                    ptype = random.choice(POWERUP_TYPES)
                    # Avoid placing on walls, food, other powerups, obstacles, snake
                    all_items = foods + power_ups_on_screen + list(active_obstacles) + list(active_maze_walls) # Include maze walls even if inactive? No, only if active.
                    # But powerups only spawn when maze *not* active, so no need for maze walls here.
                    all_items = foods + power_ups_on_screen + list(active_obstacles)

                    pos = place_item(stdscr, snake, all_items)
                    if pos: power_ups_on_screen.append((*pos, ptype))
                # Schedule next spawn time
                next_power_up_spawn_time = current_loop_time + random.uniform(15, 45) # Adjust timing range


            # --- 13. Drawing ---
            stdscr.clear()

            # Status Line
            snake_len = len(snake) if snake else 0
            status_line = f"Score: {score} | Speed: {current_timeout}ms | Len: {snake_len}"
            try: stdscr.addstr(0, 1, status_line[:sw-1])
            except curses.error: pass # Ignore drawing errors at edge

            # Effect Countdowns
            countdown_row = 1
            active_timed_effects_info = []
            for effect in active_effects:
                 if effect['type'] in TIMED_EFFECTS_TO_DISPLAY:
                     time_remaining = effect['end_time'] - current_loop_time
                     if time_remaining > 0:
                         name = POWERUP_NAMES.get(effect['type'], f"Effect {effect['type']}")
                         active_timed_effects_info.append(f"{name}: {time_remaining:.1f}s")

            # Sort effects display for consistency? Alphabetical by name?
            active_timed_effects_info.sort()

            for info_line in active_timed_effects_info:
                 if countdown_row < sh -1: # Ensure doesn't overwrite bottom edge
                    try: stdscr.addstr(countdown_row, 1, info_line[:sw-1])
                    except curses.error: pass
                    countdown_row += 1
                 else: break

            # Draw Active Effects (Maze walls/food, obstacles, enemies, meteors, balls)
            # This draws the "background" elements for the frame
            draw_active_effects(stdscr, has_colors)

            # Draw Regular Food (only if maze is not active)
            if not is_maze_active:
                food_attrib = curses.color_pair(FOOD_PAIR) if has_colors else 0
                for fx, fy in foods:
                    # Avoid drawing food over maze walls if they exist but aren't "active" (shouldn't happen often)
                    if (fx, fy) not in active_maze_walls:
                        if 0 <= fy < sh and 0 <= fx < sw:
                            try: stdscr.addch(fy, fx, FOOD_SYMBOL, food_attrib)
                            except curses.error: pass

            # Draw Powerup Pickups (?)
            for px, py, ptype in power_ups_on_screen:
                 # Determine symbol and color based on type
                 pup_symbol = UNIFIED_POWERUP_SYMBOL
                 pup_color_id_name = f"POWERUP_TYPE_{ptype}_PAIR"
                 # Use specific colors for types that have distinct visual elements
                 if ptype == 6: pup_color_id_name = "OBSTACLE_PAIR"
                 elif ptype == 7: pup_color_id_name = "METEOR_PAIR"
                 elif ptype == 8: pup_color_id_name = "MAZE_FOOD_PAIR" # Use maze color for pickup trigger too

                 # Fallback to default pair if specific pair name doesn't exist
                 pup_color_id = globals().get(pup_color_id_name, DEFAULT_PAIR)
                 pup_attrib = curses.color_pair(pup_color_id) if has_colors else 0

                 # Avoid drawing pickup over maze walls
                 if (px, py) not in active_maze_walls:
                     if 0 <= py < sh and 0 <= px < sw:
                         try: stdscr.addch(py, px, pup_symbol, pup_attrib)
                         except curses.error: pass


            # Draw Snake (on top of everything else except flash message)
            if snake:
                thick_attrib = curses.color_pair(DEFAULT_PAIR) if has_colors else 0 # Color for extra bits
                drawn_thick_segments = set() # Avoid drawing extra bits multiple times per frame
                for i, segment in enumerate(snake):
                    seg_x, seg_y = segment
                    # Draw main snake segment (using potentially overridden color)
                    if 0 <= seg_y < sh and 0 <= seg_x < sw:
                         # Avoid drawing snake body over maze walls? No, snake moves through path.
                         try: stdscr.addch(seg_y, seg_x, SNAKE_SYMBOL, snake_attrib)
                         except curses.error: pass

                    # Draw thick part if active (based on drawing logic)
                    if is_thick_active and i < len(snake) - 1:
                        next_segment = snake[i+1]
                        dx = segment[0] - next_segment[0]
                        dy = segment[1] - next_segment[1]
                        adj_x, adj_y = seg_x, seg_y
                        if dx != 0: adj_y += 1 # Offset vertically if moving horizontally
                        elif dy != 0: adj_x += 1 # Offset horizontally if moving vertically
                        adj_pos = (adj_x, adj_y)

                        # Draw only if within bounds and not already drawn this frame
                        if adj_pos not in drawn_thick_segments:
                            if 0 <= adj_y < sh and 0 <= adj_x < sw:
                                 # Avoid drawing thick part on walls?
                                 # if adj_pos not in active_maze_walls:
                                     try:
                                         stdscr.addch(adj_y, adj_x, THICK_SNAKE_EXTRA_SYMBOL, thick_attrib)
                                         drawn_thick_segments.add(adj_pos)
                                     except curses.error: pass


            # Flash Message (On top of everything)
            if flash_message and current_loop_time < flash_message_end_time:
                msg_len = len(flash_message)
                msg_y = sh // 2 ; msg_x = sw // 2 - msg_len // 2
                if msg_x < 0: msg_x = 0
                try:
                    if 0 <= msg_y < sh:
                        # Ensure message doesn't exceed screen width
                        display_msg = flash_message[:max(0, sw - 1 - msg_x)]
                        stdscr.addstr(msg_y, msg_x, display_msg, flash_message_attrib)
                except curses.error: pass # Ignore errors drawing message
            elif flash_message and current_loop_time >= flash_message_end_time:
                 flash_message = None # Clear expired message


            stdscr.refresh()
        # --- End of Inner Game Loop ---

        # --- Game Over Sequence ---
        if quit_game:
            play_again = False; continue # Exit outer loop directly

        curses.flushinp(); stdscr.nodelay(False) # Turn off nodelay for game over screen
        stdscr.clear()
        msg = f"Game Over! Final Score: {score}"
        msg_y = sh // 2 - 6 ; msg_x = sw // 2 - len(msg) // 2
        if msg_x < 0: msg_x = 0
        if msg_y < 0: msg_y = 0
        try: stdscr.addstr(msg_y, msg_x, msg)
        except curses.error: pass

        # High Score Handling
        high_scores = load_high_scores()
        is_high = check_high_score(score, high_scores)
        if is_high:
            prompt = "New High Score! Enter Name: "; player_name = get_name_input(stdscr, prompt, MAX_NAME_LENGTH)
            high_scores.append((score, player_name)); save_high_scores(high_scores)
            # Get updated sorted list for display
            high_scores_to_display = sorted(high_scores, key=lambda item: item[0], reverse=True)[:MAX_HIGH_SCORES]
        else:
            high_scores_to_display = high_scores # Display existing scores

        # Display High Scores
        hs_title = "High Scores:"; title_y = msg_y + 2; title_x = sw // 2 - len(hs_title) // 2
        if title_x < 0: title_x = 0
        if title_y < sh:
            try: stdscr.addstr(title_y, title_x, hs_title)
            except curses.error: pass

        score_start_y = title_y + 1
        last_element_y = score_start_y # Track last drawn row
        for i, (hs_score, hs_name) in enumerate(high_scores_to_display):
            score_line = f"{i + 1}. {hs_name} - {hs_score}"; line_y = score_start_y + i
            line_x = sw // 2 - len(score_line) // 2
            if line_x < 0: line_x = 0
            if line_y < sh - 2: # Leave space for prompt at bottom
                try: stdscr.addstr(line_y, line_x, score_line)
                except curses.error: pass
                last_element_y = line_y # Update last drawn row

        # Play Again Prompt
        prompt_y = last_element_y + 2
        prompt_text = "Play Again? (y/n)"
        prompt_x = sw // 2 - len(prompt_text) // 2
        if prompt_x < 0: prompt_x = 0
        if prompt_y < sh:
            try: stdscr.addstr(prompt_y, prompt_x, prompt_text)
            except curses.error: pass

        stdscr.refresh()

        # Wait for Play Again input
        while True:
            final_key = stdscr.getch()
            if final_key == ord('y') or final_key == ord('Y'):
                play_again = True; stdscr.clear(); stdscr.nodelay(True); break # Restart game
            elif final_key == ord('n') or final_key == ord('N') or final_key == ord('q'):
                play_again = False; break # Exit outer loop
    # --- End of Outer Play Again Loop ---


# --- Run the Game Entry Point ---
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Advanced Snake Game (v2.7)')
    parser.add_argument('-t', '--test', action='store_true', help='Run in test mode (activates all powerups).')
    args, unknown = parser.parse_known_args() # Use parse_known_args if other args might exist
    run_test_mode = args.test

    try:
        # Initialize curses and run the main function
        curses.wrapper(main, run_test_mode)
    except curses.error as e:
        # Handle potential curses errors gracefully
        print("\n---------------------", file=sys.stderr)
        print(f"A curses error occurred: {e}", file=sys.stderr)
        print("This might happen if the terminal was resized during the game,", file=sys.stderr)
        print("or if the terminal type is not fully supported.", file=sys.stderr)
        print("Try resizing terminal or using a different terminal emulator.", file=sys.stderr)
        print("---------------------\n", file=sys.stderr)
        # traceback.print_exc(file=sys.stderr) # Optional: full traceback
    except Exception as e:
        # Catch any other unexpected errors
        print("\n---------------------", file=sys.stderr)
        print(f"An unexpected error occurred: {type(e).__name__}: {e}", file=sys.stderr)
        print("---------------------\n", file=sys.stderr)
        traceback.print_exc(file=sys.stderr) # Print detailed traceback
    finally:
        # Cleanup message regardless of how the game exits
        # curses.endwin() is handled by curses.wrapper()
        print("\nGame exited.")
