import os
import io
import sys
import wave
import struct
import random
import math
import colorsys
import copy
import pickle
import shutil
import tempfile
import threading
import subprocess
import webbrowser
import tkinter as tk
from tkinter import filedialog, simpledialog, colorchooser, ttk
from PIL import Image, ImageTk, ImageDraw, ImageOps, ImageFilter, ImageFont
import time
import queue
import traceback
import json

def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

try:
    import moviepy.editor as mp
    HAS_MOVIEPY = True
except ImportError:
    HAS_MOVIEPY = False
    print("Warning: moviepy not installed. Video export will use ffmpeg fallback.")

def upload_file(file_path, userhash=None):
    if not shutil.which("curl"):
        return "Error: 'curl' is not installed on this system. Upload failed."
    if not os.path.exists(file_path):
        return f"Error: File '{file_path}' not found."
    cmd = ["curl", "-F", "reqtype=fileupload"]
    if userhash:
        cmd.extend(["-F", f"userhash={userhash}"])
    cmd.extend(["-F", f"fileToUpload=@{file_path}", "https://catbox.moe/user/api.php"])
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        response = result.stdout.strip()
        if response.startswith("https://files.catbox.moe/"):
            webbrowser.open(response)
            return response
        else:
            return f"Error from Catbox API: {response}"
    except subprocess.CalledProcessError as e:
        return f"Error running curl: {e.stderr if e.stderr else str(e)}"
    except Exception as e:
        return f"Unexpected error during upload: {str(e)}"

SCRIPT_DIR = resource_path(".")
SETTINGS_FILE = os.path.join(SCRIPT_DIR, "settings.txt")
SHORTCUTS_FILE = os.path.join(SCRIPT_DIR, "shortcuts.txt")

try:
    NEAREST_NEIGHBOR = Image.Resampling.NEAREST
    BILINEAR = Image.Resampling.BILINEAR
except AttributeError:
    NEAREST_NEIGHBOR = Image.NEAREST
    BILINEAR = Image.BILINEAR

try:
    import pygame
    pygame.mixer.init()
    HAS_PYGAME = True
except ImportError:
    HAS_PYGAME = False

class Layer:
    def __init__(self, layer_id, name, width=800, height=600):
        self.id = layer_id
        self.name = name
        self.visible = True
        self.locked = False
        self.image = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    def clone(self):
        new_layer = Layer(self.id, self.name, self.image.width, self.image.height)
        new_layer.visible = self.visible
        new_layer.locked = self.locked
        new_layer.image = self.image.copy()
        return new_layer

class Frame:
    def __init__(self, frame_id, layers):
        self.id = frame_id
        self.layers = [layer.clone() for layer in layers]
    def get_layer(self, layer_id):
        for layer in self.layers:
            if layer.id == layer_id:
                return layer
        return None

class FreenimateApp:
    VIDEO_FORMATS = {
        "MPEG-4 (.mp4)": {"ext": "mp4", "codec": "libx264", "audio_codec": "aac"},
        "QuickTime Movie (.mov)": {"ext": "mov", "codec": "libx264", "audio_codec": "aac"},
        "Audio Video Interleave (.avi)": {"ext": "avi", "codec": "mpeg4", "audio_codec": "mp3"},
        "Matroska Video (.mkv)": {"ext": "mkv", "codec": "libx264", "audio_codec": "aac"},
        "Web Media (.webm)": {"ext": "webm", "codec": "libvpx-vp9", "audio_codec": "libopus"},
        "Windows Media Video (.wmv)": {"ext": "wmv", "codec": "wmv2", "audio_codec": "wmav2"},
    }

    AUDIO_PX_PER_SEC = 80
    AUDIO_TRACK_H = 76
    AUDIO_RULER_H = 26
    AUDIO_TRACK_PAD = 8
    AUDIO_EDGE = 8
    AUDIO_VOL_ZONE = 16
    AUDIO_NUM_TRACKS = 4

    def __init__(self, root):
        self.root = root
        self.root.title("Freenimate")
        self.root.geometry("1280x850")
        self.root.configure(bg="#3a3a3a")

        self.settings = self.load_settings()
        self.render_mode = self.settings.get("render_mode", "CPU")
        self.canvas_width = self.settings.get("canvas_width", 800)
        self.canvas_height = self.settings.get("canvas_height", 600)

        self.current_tool = "pencil"
        self.current_color = "#e61a1a"
        self.brush_size = self.settings.get("brush_size", 12)
        self.brush_mode = self.settings.get("brush_mode", "pixel")
        self.ui_scale = self.settings.get("ui_scale", 1.0)
        self.fps = self.settings.get("fps", 12)
        self.onion_skin = self.settings.get("onion_skin", True)
        self.is_playing = False
        self.playback_job = None
        self.playback_start_time = 0
        self.playback_elapsed_time = 0

        self.zoom_level = 1.0
        self.pan_offset_x = 0
        self.pan_offset_y = 0
        self.start_pan_x = 0
        self.start_pan_y = 0

        self.next_layer_id = 4
        self.base_layers = [
            Layer(3, "Layer 3", self.canvas_width, self.canvas_height),
            Layer(2, "Layer 2", self.canvas_width, self.canvas_height),
            Layer(1, "Layer 1", self.canvas_width, self.canvas_height)
        ]
        self.active_layer_id = 1
        self.frames = [Frame(1, self.base_layers)]
        self.active_frame_idx = 0

        self.undo_stack = []
        self.redo_stack = []

        self.swatch_colors = [
            "#e61a1a", "#ff7315", "#f2ee0c",
            "#22b14c", "#a8e61d", "#87ceeb",
            "#000000", "#ffffff", "#8a3ab9"
        ]
        self.swatch_buttons = []
        self.save_index = 0

        self.start_x = None
        self.start_y = None
        self.last_x = None
        self.last_y = None
        self.preview_shape_id = None

        self.icons = {}
        self.tool_buttons = {}
        self.playback_buttons = []

        self.audio_clips = []
        self.audio_clip_counter = 0
        self.waveform_cache = {}
        self.duration_cache = {}
        self.audio_win = None
        self._audio_drag = None
        self._clip_drag = None
        self._audio_redraw_job = None
        self._preview_process = None
        self._clip_drag_ghost = None
        self._playback_audio_processes = []
        self._audio_playback_threads = []
        self._credits_window = None
        self._credits_process = None
        self._credits_audio = None
        self._credits_photo = None
        self._credits_queue = queue.Queue(maxsize=3)
        self._credits_stop = threading.Event()
        self._audio_sync_lock = threading.Lock()
        self._audio_started = False
        self._audio_preinit_done = False
        self._pygame_sounds = {}

        self._scroll_position = 0

        self.brushes = {}
        self.brush_names = []
        self.current_brush_name = "Mosaic"
        self.brush_preview_images = {}

        self.shortcuts = self.load_shortcuts()
        self.load_brushes()

        self.text_mode = False
        self.text_string = ""
        self.text_position = (0, 0)
        self.text_font = "Arial"
        self.text_size = 24
        self.text_bold = False
        self.text_italic = False
        self.text_underline = False
        self.text_strikethrough = False
        self.text_control_window = None
        self.text_gizmos = []
        self.text_is_editing = False
        self.text_scale_mode = False
        self.text_original_bbox = None
        self.text_drag_start = None
        self.text_info = None
        self.text_applied = False
        self.text_overlay_id = None
        self.text_gizmo_ids = []
        self.text_layer_image = None

        self.selection_start = None
        self.selection_end = None
        self.selection_rect = None
        self.is_dragging_selection = False
        self.selection_offset = None
        self.selected_pixels = None
        self.selection_active = False
        self.selection_original_position = None

        self.blur_radius = 5
        self.pixel_brush_enabled = False
        self.smudge_strength = 0.65

        self.bind_shortcuts()
        self.create_menu()
        self.create_ui()
        self.bind_canvas_events()
        self.refresh_layers_ui()
        self.refresh_timeline_ui()
        self.render_canvas()
        self._preinit_audio()
        self._check_external_tools()

    def _check_external_tools(self):
        if not shutil.which("curl"):
            self.show_alert("Missing curl",
                "curl is not installed. Catbox upload will not work.\n"
                "Please install curl from https://curl.se/", is_error=False)
        if not shutil.which("ffmpeg"):
            self.show_alert("Missing ffmpeg",
                "ffmpeg is not installed. Some features (video import, credits, how-to) may not work.\n"
                "Please install ffmpeg from https://ffmpeg.org/", is_error=False)

    # ---------- Shortcuts ----------
    def load_shortcuts(self):
        default = {
            "Ctrl+Z": "undo", "Ctrl+Shift+Z": "redo", "Ctrl+S": "save_project",
            "Ctrl+O": "load_project", "Ctrl+N": "new_project", "Ctrl+E": "export_video_with_audio",
            "Ctrl+U": "upload_to_catbox", "Ctrl+G": "export_gif", "Ctrl+P": "export_png_sequence",
            "Ctrl+1": "tool_pencil", "Ctrl+2": "tool_eraser", "Ctrl+3": "tool_marquee",
            "Ctrl+4": "tool_smudge", "Ctrl+5": "tool_blur", "Ctrl+6": "tool_text",
            "Ctrl+7": "tool_shape", "Ctrl+8": "tool_zoom", "Ctrl+9": "tool_eyedropper",
            "Ctrl+0": "tool_selection", "Space": "toggle_play",
            "Left": "previous_frame", "Right": "next_frame",
            "Home": "first_frame", "End": "last_frame", "Delete": "delete_frame"
        }
        if not os.path.exists(SHORTCUTS_FILE):
            return default
        try:
            with open(SHORTCUTS_FILE, 'r') as f:
                loaded = json.load(f)
                for key, value in default.items():
                    if key not in loaded:
                        loaded[key] = value
                return loaded
        except:
            return default

    def save_shortcuts(self, shortcuts=None):
        if shortcuts is None:
            shortcuts = self.shortcuts
        try:
            with open(SHORTCUTS_FILE, 'w') as f:
                json.dump(shortcuts, f, indent=4)
            return True
        except:
            return False

    def bind_shortcuts(self):
        self.shortcut_functions = {
            "undo": self.undo, "redo": self.redo,
            "save_project": self.save_project, "load_project": self.load_project,
            "new_project": self.new_project_dialog,
            "export_video_with_audio": self.export_video_with_audio,
            "upload_to_catbox": self.upload_to_catbox,
            "export_gif": self.export_gif, "export_png_sequence": self.export_png_sequence,
            "tool_pencil": lambda: self.select_tool("pencil"),
            "tool_eraser": lambda: self.select_tool("eraser"),
            "tool_marquee": lambda: self.select_tool("marquee"),
            "tool_smudge": lambda: self.select_tool("smudge"),
            "tool_blur": lambda: self.select_tool("blur"),
            "tool_text": lambda: self.select_tool("text"),
            "tool_shape": lambda: self.select_tool("shape"),
            "tool_zoom": lambda: self.select_tool("zoom"),
            "tool_eyedropper": lambda: self.select_tool("eyedropper"),
            "tool_selection": lambda: self.select_tool("selection"),
            "toggle_play": self.toggle_play,
            "previous_frame": lambda: self.select_frame(max(0, self.active_frame_idx - 1)),
            "next_frame": lambda: self.select_frame(min(len(self.frames) - 1, self.active_frame_idx + 1)),
            "first_frame": self.first_frame, "last_frame": self.last_frame,
            "delete_frame": self.delete_frame
        }
        self._bind_shortcuts_to_root()

    def _bind_shortcuts_to_root(self):
        for key, action in self.shortcuts.items():
            tk_key = key
            if "Ctrl" in tk_key:
                tk_key = tk_key.replace("Ctrl", "Control")
            if tk_key == "Space":
                tk_key = "<space>"
            elif tk_key == "Left":
                tk_key = "<Left>"
            elif tk_key == "Right":
                tk_key = "<Right>"
            elif tk_key == "Home":
                tk_key = "<Home>"
            elif tk_key == "End":
                tk_key = "<End>"
            elif tk_key == "Delete":
                tk_key = "<Delete>"
            else:
                parts = tk_key.split("+")
                if len(parts) > 1:
                    mods = []
                    key_name = parts[-1]
                    for p in parts[:-1]:
                        if p == "Control":
                            mods.append("Control")
                        elif p == "Shift":
                            mods.append("Shift")
                        elif p == "Alt":
                            mods.append("Alt")
                    if len(key_name) == 1 and key_name.isalpha():
                        key_name = key_name.lower()
                    tk_key = "<" + "-".join(mods) + "-" + key_name + ">"
                else:
                    if len(tk_key) == 1 and tk_key.isalpha():
                        tk_key = tk_key.lower()
                    tk_key = "<" + tk_key + ">"
            try:
                self.root.bind_all(tk_key, self._make_shortcut_callback(action))
            except Exception as e:
                print(f"Failed to bind {tk_key}: {e}")

    def _make_shortcut_callback(self, action):
        def callback(event):
            if action in self.shortcut_functions:
                if action.startswith("tool_"):
                    tool_id = action.replace("tool_", "")
                    self.select_tool(tool_id)
                else:
                    self.shortcut_functions[action]()
            return "break"
        return callback

    # ---------- Settings ----------
    def load_settings(self):
        default = {
            "render_mode": "CPU", "canvas_width": 800, "canvas_height": 600,
            "ui_scale": 1.0, "fps": 12, "onion_skin": True,
            "brush_size": 12, "brush_mode": "pixel"
        }
        if not os.path.exists(SETTINGS_FILE):
            self.save_settings(default)
            return default
        try:
            with open(SETTINGS_FILE, 'r') as f:
                settings = json.load(f)
                for key, value in default.items():
                    if key not in settings:
                        settings[key] = value
                return settings
        except:
            return default

    def save_settings(self, settings=None):
        if settings is None:
            settings = {
                "render_mode": self.render_mode,
                "canvas_width": self.canvas_width,
                "canvas_height": self.canvas_height,
                "ui_scale": self.ui_scale,
                "fps": self.fps,
                "onion_skin": self.onion_skin,
                "brush_size": self.brush_size,
                "brush_mode": self.brush_mode
            }
        try:
            with open(SETTINGS_FILE, 'w') as f:
                json.dump(settings, f, indent=4)
            return True
        except:
            return False

    def apply_render_mode(self):
        print(f"Render mode set to: {self.render_mode}")

    # ---------- Brushes ----------
    def load_brushes(self):
        brush_dir = resource_path("brushes")
        if not os.path.exists(brush_dir):
            os.makedirs(brush_dir, exist_ok=True)
        valid_ext = {".png", ".bmp", ".gif", ".jpg", ".jpeg"}
        brush_files = [f for f in os.listdir(brush_dir) if os.path.splitext(f)[1].lower() in valid_ext]
        for brush_file in brush_files:
            try:
                brush_path = os.path.join(brush_dir, brush_file)
                img = Image.open(brush_path).convert("RGBA")
                brush_name = os.path.splitext(brush_file)[0]
                self.brushes[brush_name] = img
                self.brush_names.append(brush_name)
            except:
                pass
        if not self.brushes:
            default_brush = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
            draw = ImageDraw.Draw(default_brush)
            draw.ellipse([4, 4, 60, 60], fill=(255, 255, 255, 255))
            self.brushes["Mosaic"] = default_brush
            self.brush_names.append("Mosaic")
        if "Pixel Brush" not in self.brush_names:
            pixel_brush = Image.new("RGBA", (2, 2), (255, 255, 255, 255))
            self.brushes["Pixel Brush"] = pixel_brush
            self.brush_names.append("Pixel Brush")
        if "Pen" not in self.brush_names:
            pen_img = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
            draw = ImageDraw.Draw(pen_img)
            draw.ellipse([4, 4, 60, 60], fill=(255, 255, 255, 255))
            self.brushes["Pen"] = pen_img
            self.brush_names.append("Pen")
        if self.brush_names:
            self.current_brush_name = self.brush_names[0]
            self.current_brush = self.brushes[self.current_brush_name]

    # ---------- Dialogs ----------
    def show_confirm_dialog(self, title, message, yes_callback):
        win = tk.Toplevel(self.root)
        win.title(title)
        win.geometry("460x180")
        win.configure(bg="#2a2a2a")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)
        win.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        win.geometry(f"+{px + (pw // 2) - 230}+{py + (ph // 2) - 90}")
        content_f = tk.Frame(win, bg="#2a2a2a", padx=20, pady=20)
        content_f.pack(expand=True, fill=tk.BOTH)
        alert_icon = self.load_icon("smileyalert.png", (48, 48))
        if alert_icon:
            img_lbl = tk.Label(content_f, image=alert_icon, bg="#2a2a2a")
            img_lbl.image = alert_icon
            img_lbl.pack(side=tk.LEFT, padx=(0, 15), anchor="center")
        else:
            img_lbl = tk.Label(content_f, text="[?]", font=("Arial", 16, "bold"), bg="#2a2a2a", fg="#ffcc00")
            img_lbl.pack(side=tk.LEFT, padx=(0, 15), anchor="center")
        msg_lbl = tk.Label(content_f, text=message, bg="#2a2a2a", fg="white",
                           font=("Arial", 10, "bold"), wraplength=320, justify=tk.LEFT)
        msg_lbl.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        btn_f = tk.Frame(win, bg="#1e1e1e", pady=10, padx=15)
        btn_f.pack(fill=tk.X, side=tk.BOTTOM)
        def on_yes():
            win.destroy()
            yes_callback()
        def on_no():
            win.destroy()
        tk.Button(btn_f, text="Yes", bg="#007acc", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=on_yes).pack(side=tk.RIGHT, padx=(6,0))
        tk.Button(btn_f, text="No", bg="#444444", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=on_no).pack(side=tk.RIGHT)

    def _preinit_audio(self):
        if HAS_PYGAME:
            try:
                pygame.mixer.init()
            except:
                pass

    def load_icon(self, filename, base_size=(32, 32)):
        scaled_w = max(1, int(base_size[0] * self.ui_scale))
        scaled_h = max(1, int(base_size[1] * self.ui_scale))
        cache_key = f"{filename}_{scaled_w}x{scaled_h}"
        if cache_key in self.icons:
            return self.icons[cache_key]
        paths = [
            resource_path(os.path.join("images", filename)),
            resource_path(filename),
            os.path.join(os.getcwd(), "images", filename),
            os.path.join(os.getcwd(), filename)
        ]
        for path in paths:
            if os.path.exists(path):
                try:
                    pil_img = Image.open(path)
                    resized = pil_img.resize((scaled_w, scaled_h), NEAREST_NEIGHBOR)
                    tk_img = ImageTk.PhotoImage(resized)
                    self.icons[cache_key] = tk_img
                    return tk_img
                except:
                    pass
        return None

    def show_alert(self, title, message, is_error=False):
        win = tk.Toplevel(self.root)
        win.title(title)
        win.geometry("460x200")
        win.configure(bg="#2a2a2a")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)
        win.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        win.geometry(f"+{px + (pw // 2) - 230}+{py + (ph // 2) - 100}")
        content_f = tk.Frame(win, bg="#2a2a2a", padx=20, pady=20)
        content_f.pack(expand=True, fill=tk.BOTH)
        icon_name = "smileywarn.png" if is_error else "smileyalert.png"
        alert_icon = self.load_icon(icon_name, (48, 48))
        if alert_icon:
            img_lbl = tk.Label(content_f, image=alert_icon, bg="#2a2a2a")
            img_lbl.image = alert_icon
            img_lbl.pack(side=tk.LEFT, padx=(0, 15), anchor="center")
        else:
            img_lbl = tk.Label(content_f, text="[!]" if not is_error else "[X]",
                               font=("Arial", 16, "bold"), bg="#2a2a2a",
                               fg="#ffcc00" if not is_error else "#ff4444")
            img_lbl.pack(side=tk.LEFT, padx=(0, 15), anchor="center")
        msg_lbl = tk.Label(content_f, text=message, bg="#2a2a2a", fg="white",
                           font=("Arial", 10, "bold"), wraplength=320, justify=tk.LEFT)
        msg_lbl.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        btn_f = tk.Frame(win, bg="#1e1e1e", pady=10, padx=15)
        btn_f.pack(fill=tk.X, side=tk.BOTTOM)
        tk.Button(btn_f, text="OK", bg="#007acc", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=win.destroy).pack(side=tk.RIGHT)

    def show_error_dialog(self, error_message):
        self.play_sound("traceback.mp3")
        self.show_alert("Error", error_message, is_error=True)

    def play_sound(self, filename):
        search_paths = [
            resource_path(os.path.join("sounds", filename)),
            resource_path(filename),
            os.path.join(os.getcwd(), "sounds", filename),
            os.path.join(os.getcwd(), filename),
        ]
        sound_path = next((p for p in search_paths if os.path.exists(p)), None)
        if sound_path:
            self.play_audio_file(sound_path)

    def play_audio_file(self, path, volume=1.0, start_offset=0.0, duration=None):
        if not path or not os.path.isfile(path):
            return
        def _play():
            try:
                if HAS_PYGAME:
                    try:
                        if path not in self._pygame_sounds:
                            self._pygame_sounds[path] = pygame.mixer.Sound(path)
                        sound = self._pygame_sounds[path]
                        if volume != 1.0:
                            sound.set_volume(min(1.0, max(0.0, volume)))
                        sound.play()
                        if duration is not None:
                            time.sleep(duration)
                            sound.stop()
                        return
                    except:
                        pass
                ffplay = shutil.which("ffplay")
                if ffplay:
                    cmd = [ffplay, "-nodisp", "-autoexit", "-loglevel", "quiet", "-vn",
                           "-analyzeduration", "0", "-probesize", "32", "-flags", "low_delay",
                           "-fflags", "nobuffer", "-avioflags", "direct"]
                    if volume != 1.0:
                        cmd.extend(["-af", f"volume={volume}"])
                    if start_offset > 0:
                        cmd.extend(["-ss", str(start_offset)])
                    if duration is not None:
                        cmd.extend(["-t", str(duration)])
                    cmd.append(path)
                    proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    self._preview_process = proc
                    proc.wait()
                    if self._preview_process is proc:
                        self._preview_process = None
                    return
                if sys.platform.startswith("win"):
                    if os.path.splitext(path)[1].lower() == ".wav":
                        import winsound
                        winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_NODEFAULT)
                        return
                if sys.platform == "darwin":
                    subprocess.Popen(["afplay", path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    return
                for cmd in (["paplay"], ["aplay", "-q"]):
                    if shutil.which(cmd[0]):
                        subprocess.Popen(cmd + [path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                        return
            except:
                pass
        threading.Thread(target=_play, daemon=True).start()

    def stop_audio_preview(self):
        try:
            if HAS_PYGAME:
                pygame.mixer.stop()
        except:
            pass
        try:
            if sys.platform.startswith("win"):
                import winsound
                winsound.PlaySound(None, winsound.SND_PURGE)
        except:
            pass
        proc = self._preview_process
        self._preview_process = None
        if proc is not None:
            try:
                if proc.poll() is None:
                    proc.terminate()
            except:
                pass

    # ---------- Shortcut Editor ----------
    def open_shortcut_editor(self):
        win = tk.Toplevel(self.root)
        win.title("Shortcut Editor")
        win.geometry("520x460")
        win.configure(bg="#2a2a2a")
        win.transient(self.root)
        win.grab_set()
        win.resizable(True, True)
        win.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        win.geometry(f"+{px + (pw // 2) - 260}+{py + (ph // 2) - 230}")
        tk.Label(win, text="Shortcut Editor", font=("Arial", 14, "bold"),
                 bg="#2a2a2a", fg="white").pack(pady=10)
        scroll_frame = tk.Frame(win, bg="#2a2a2a")
        scroll_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        canvas = tk.Canvas(scroll_frame, bg="#2a2a2a", highlightthickness=0)
        scrollbar = tk.Scrollbar(scroll_frame, orient=tk.VERTICAL, command=canvas.yview)
        inner_frame = tk.Frame(canvas, bg="#2a2a2a")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas_window = canvas.create_window((0, 0), window=inner_frame, anchor="nw")
        def on_frame_configure(event):
            canvas.configure(scrollregion=canvas.bbox("all"))
        def on_canvas_configure(event):
            canvas.itemconfig(canvas_window, width=max(1, event.width))
        inner_frame.bind("<Configure>", on_frame_configure)
        canvas.bind("<Configure>", on_canvas_configure)
        def on_shortcut_mousewheel(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            return "break"
        def bind_scroll_recursive(widget):
            widget.bind("<MouseWheel>", on_shortcut_mousewheel, add="+")
            for child in widget.winfo_children():
                bind_scroll_recursive(child)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        shortcut_entries = []
        shortcut_labels = {
            "undo": "Undo", "redo": "Redo", "save_project": "Save Project",
            "load_project": "Load Project", "new_project": "New Project",
            "export_video_with_audio": "Export Video", "upload_to_catbox": "Upload to Catbox",
            "export_gif": "Export GIF", "export_png_sequence": "Export PNG Sequence",
            "tool_pencil": "Pencil Tool", "tool_eraser": "Eraser Tool",
            "tool_marquee": "Marquee Tool", "tool_smudge": "Smudge Tool",
            "tool_blur": "Blur Tool", "tool_text": "Text Tool",
            "tool_shape": "Shape Tool", "tool_zoom": "Zoom Tool",
            "tool_eyedropper": "Eyedropper Tool", "tool_selection": "Selection Tool",
            "toggle_play": "Play/Pause", "previous_frame": "Previous Frame",
            "next_frame": "Next Frame", "first_frame": "First Frame",
            "last_frame": "Last Frame", "delete_frame": "Delete Frame"
        }
        for action in sorted(shortcut_labels.keys()):
            label_text = shortcut_labels[action]
            current_shortcut = None
            for key, val in self.shortcuts.items():
                if val == action:
                    current_shortcut = key
                    break
            if current_shortcut is None:
                continue
            row_frame = tk.Frame(inner_frame, bg="#333", padx=5, pady=3)
            row_frame.pack(fill=tk.X, pady=2)
            tk.Label(row_frame, text=label_text, bg="#333", fg="white",
                     font=("Arial", 9), width=20, anchor="w").pack(side=tk.LEFT, padx=5)
            shortcut_var = tk.StringVar(value=current_shortcut)
            entry = tk.Entry(row_frame, textvariable=shortcut_var, bg="#444", fg="white",
                             font=("Arial", 9), width=15, relief=tk.FLAT)
            entry.pack(side=tk.RIGHT, padx=5)
            shortcut_entries.append((action, shortcut_var))
        bind_scroll_recursive(inner_frame)
        btn_frame = tk.Frame(win, bg="#2a2a2a")
        btn_frame.pack(fill=tk.X, pady=10)
        def on_save():
            for action, var in shortcut_entries:
                new_shortcut = var.get().strip()
                if new_shortcut:
                    for key, val in list(self.shortcuts.items()):
                        if val == action:
                            del self.shortcuts[key]
                            break
                    self.shortcuts[new_shortcut] = action
            self.save_shortcuts()
            self.bind_shortcuts()
            win.destroy()
            self.show_alert("Shortcuts Saved", "Shortcuts have been updated successfully!")
        def on_reset():
            default = {
                "Ctrl+Z": "undo", "Ctrl+Shift+Z": "redo", "Ctrl+S": "save_project",
                "Ctrl+O": "load_project", "Ctrl+N": "new_project",
                "Ctrl+E": "export_video_with_audio", "Ctrl+U": "upload_to_catbox",
                "Ctrl+G": "export_gif", "Ctrl+P": "export_png_sequence",
                "Ctrl+1": "tool_pencil", "Ctrl+2": "tool_eraser",
                "Ctrl+3": "tool_marquee", "Ctrl+4": "tool_smudge",
                "Ctrl+5": "tool_blur", "Ctrl+6": "tool_text",
                "Ctrl+7": "tool_shape", "Ctrl+8": "tool_zoom",
                "Ctrl+9": "tool_eyedropper", "Ctrl+0": "tool_selection",
                "Space": "toggle_play", "Left": "previous_frame",
                "Right": "next_frame", "Home": "first_frame",
                "End": "last_frame", "Delete": "delete_frame"
            }
            self.shortcuts = default
            self.save_shortcuts()
            self.bind_shortcuts()
            win.destroy()
            self.show_alert("Shortcuts Reset", "Shortcuts have been reset to defaults!")
        tk.Button(btn_frame, text="Save", bg="#007acc", fg="white",
                  font=("Arial", 9, "bold"), padx=20, pady=5,
                  relief=tk.FLAT, command=on_save).pack(side=tk.LEFT, padx=10)
        tk.Button(btn_frame, text="Reset to Defaults", bg="#444", fg="white",
                  font=("Arial", 9, "bold"), padx=20, pady=5,
                  relief=tk.FLAT, command=on_reset).pack(side=tk.LEFT, padx=10)
        tk.Button(btn_frame, text="Cancel", bg="#555", fg="white",
                  font=("Arial", 9, "bold"), padx=20, pady=5,
                  relief=tk.FLAT, command=win.destroy).pack(side=tk.RIGHT, padx=10)

    # ---------- New Project ----------
    def new_project_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("New Project")
        win.geometry("400x250")
        win.configure(bg="#2a2a2a")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)
        win.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        win.geometry(f"+{px + (pw // 2) - 200}+{py + (ph // 2) - 125}")
        tk.Label(win, text="New Project", font=("Arial", 14, "bold"),
                 bg="#2a2a2a", fg="white").pack(pady=15)
        dim_frame = tk.Frame(win, bg="#2a2a2a")
        dim_frame.pack(pady=10)
        tk.Label(dim_frame, text="Width:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=5)
        width_var = tk.IntVar(value=self.canvas_width)
        width_spin = tk.Spinbox(dim_frame, from_=100, to=4096, width=8,
                                textvariable=width_var, bg="#333", fg="white",
                                relief=tk.FLAT)
        width_spin.pack(side=tk.LEFT, padx=5)
        tk.Label(dim_frame, text="Height:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=10)
        height_var = tk.IntVar(value=self.canvas_height)
        height_spin = tk.Spinbox(dim_frame, from_=100, to=4096, width=8,
                                 textvariable=height_var, bg="#333", fg="white",
                                 relief=tk.FLAT)
        height_spin.pack(side=tk.LEFT, padx=5)
        preset_frame = tk.Frame(win, bg="#2a2a2a")
        preset_frame.pack(pady=10)
        tk.Label(preset_frame, text="Presets:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=5)
        def set_preset(w, h):
            width_var.set(w)
            height_var.set(h)
        presets = [
            ("HD (1280x720)", 1280, 720),
            ("Full HD (1920x1080)", 1920, 1080),
            ("4K (3840x2160)", 3840, 2160),
            ("Square (1024x1024)", 1024, 1024),
            ("Instagram (1080x1350)", 1080, 1350),
        ]
        preset_dropdown = ttk.Combobox(preset_frame, values=[p[0] for p in presets],
                                       width=18, state="readonly")
        preset_dropdown.pack(side=tk.LEFT, padx=5)
        preset_dropdown.bind("<<ComboboxSelected>>", lambda e: set_preset(
            presets[preset_dropdown.current()][1],
            presets[preset_dropdown.current()][2]
        ))
        fps_frame = tk.Frame(win, bg="#2a2a2a")
        fps_frame.pack(pady=5)
        tk.Label(fps_frame, text="FPS:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=5)
        fps_var = tk.IntVar(value=self.fps)
        fps_spin = tk.Spinbox(fps_frame, from_=1, to=60, width=6,
                              textvariable=fps_var, bg="#333", fg="white",
                              relief=tk.FLAT)
        fps_spin.pack(side=tk.LEFT, padx=5)
        def on_create():
            new_width = width_var.get()
            new_height = height_var.get()
            new_fps = fps_var.get()
            if len(self.frames) > 1:
                self.show_confirm_dialog(
                    "Create New Project",
                    f"This will clear your current project.\nNew canvas: {new_width}x{new_height}\nFPS: {new_fps}\n\nAre you sure?",
                    lambda: self.execute_new_project(new_width, new_height, new_fps, win)
                )
            else:
                self.execute_new_project(new_width, new_height, new_fps, win)
        def on_cancel():
            win.destroy()
        btn_frame = tk.Frame(win, bg="#2a2a2a")
        btn_frame.pack(pady=15)
        tk.Button(btn_frame, text="Create", bg="#007acc", fg="white",
                  font=("Arial", 10, "bold"), padx=30, pady=8,
                  relief=tk.FLAT, command=on_create).pack(side=tk.LEFT, padx=10)
        tk.Button(btn_frame, text="Cancel", bg="#555", fg="white",
                  font=("Arial", 10, "bold"), padx=20, pady=8,
                  relief=tk.FLAT, command=on_cancel).pack(side=tk.LEFT, padx=10)

    def execute_new_project(self, width, height, fps, dialog_win):
        dialog_win.destroy()
        self.canvas_width = width
        self.canvas_height = height
        self.fps = fps
        self.next_layer_id = 4
        self.base_layers = [
            Layer(3, "Layer 3", self.canvas_width, self.canvas_height),
            Layer(2, "Layer 2", self.canvas_width, self.canvas_height),
            Layer(1, "Layer 1", self.canvas_width, self.canvas_height)
        ]
        self.active_layer_id = 1
        self.frames = [Frame(1, self.base_layers)]
        self.active_frame_idx = 0
        self.undo_stack = []
        self.redo_stack = []
        self.audio_clips = []
        self.audio_clip_counter = 0
        self.waveform_cache = {}
        self.duration_cache = {}
        self.zoom_level = 1.0
        self.pan_offset_x = 0
        self.pan_offset_y = 0
        self.stop_playback_audio()
        self.refresh_timeline_ui()
        self.refresh_layers_ui()
        self.render_canvas()
        self.show_alert("New Project", f"New project created!\n{width}x{height} @ {fps} FPS")

    # ---------- Upload ----------
    def upload_to_catbox(self):
        if not HAS_MOVIEPY:
            self.show_alert("MoviePy Missing", "moviepy is not installed. Please install it with:\npip install moviepy")
            return
        self.show_upload_dialog()

    def show_upload_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("Export & Upload to Catbox")
        win.geometry("420x480")
        win.configure(bg="#2a2a2a")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)
        win.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        win.geometry(f"+{px + (pw // 2) - 210}+{py + (ph // 2) - 240}")
        tk.Label(win, text="Choose a video format:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).pack(pady=(15, 8), padx=15, anchor="w")
        format_var = tk.StringVar(value=next(iter(self.VIDEO_FORMATS)))
        list_frame = tk.Frame(win, bg="#2a2a2a")
        list_frame.pack(fill=tk.X, padx=15)
        for label in self.VIDEO_FORMATS:
            rb = tk.Radiobutton(list_frame, text=label, variable=format_var, value=label,
                                bg="#2a2a2a", fg="white", selectcolor="#1e1e1e",
                                activebackground="#2a2a2a", activeforeground="white",
                                font=("Arial", 9), anchor="w")
            rb.pack(fill=tk.X, pady=2)
        upload_frame = tk.LabelFrame(win, text="Upload to Catbox", bg="#2a2a2a", fg="white", padx=10, pady=10)
        upload_frame.pack(fill=tk.X, padx=15, pady=10)
        upload_var = tk.BooleanVar(value=False)
        upload_check = tk.Checkbutton(upload_frame, text="Upload video to Catbox.moe",
                                      variable=upload_var, bg="#2a2a2a", fg="white",
                                      selectcolor="#1e1e1e", activebackground="#2a2a2a",
                                      activeforeground="white", command=lambda: toggle_upload_options())
        upload_check.pack(anchor="w")
        auth_frame = tk.Frame(upload_frame, bg="#2a2a2a")
        auth_frame.pack(fill=tk.X, pady=5)
        auth_var = tk.StringVar(value="anonymous")
        anonymous_rb = tk.Radiobutton(auth_frame, text="Anonymous", variable=auth_var, value="anonymous",
                                      bg="#2a2a2a", fg="white", selectcolor="#1e1e1e",
                                      activebackground="#2a2a2a", activeforeground="white")
        anonymous_rb.pack(side=tk.LEFT, padx=10)
        account_rb = tk.Radiobutton(auth_frame, text="Catbox Account", variable=auth_var, value="account",
                                    bg="#2a2a2a", fg="white", selectcolor="#1e1e1e",
                                    activebackground="#2a2a2a", activeforeground="white")
        account_rb.pack(side=tk.LEFT, padx=10)
        userhash_entry = tk.Entry(upload_frame, bg="#444", fg="white", width=30,
                                  font=("Arial", 9), relief=tk.FLAT)
        userhash_entry.pack(pady=5, fill=tk.X)
        userhash_entry.insert(0, "Userhash (if account)")
        userhash_entry.config(state="disabled", fg="#888")
        def toggle_upload_options():
            if upload_var.get():
                auth_frame.pack(fill=tk.X, pady=5)
                userhash_entry.pack(pady=5, fill=tk.X)
                if auth_var.get() == "account":
                    userhash_entry.config(state="normal", fg="white")
                    userhash_entry.delete(0, tk.END)
                else:
                    userhash_entry.config(state="disabled", fg="#888")
                    userhash_entry.delete(0, tk.END)
                    userhash_entry.insert(0, "Userhash (if account)")
            else:
                auth_frame.pack_forget()
                userhash_entry.pack_forget()
        def on_auth_change(*args):
            if auth_var.get() == "account":
                userhash_entry.config(state="normal", fg="white")
                userhash_entry.delete(0, tk.END)
            else:
                userhash_entry.config(state="disabled", fg="#888")
                userhash_entry.delete(0, tk.END)
                userhash_entry.insert(0, "Userhash (if account)")
        auth_var.trace_add("write", on_auth_change)
        btn_f = tk.Frame(win, bg="#1e1e1e", pady=10, padx=15)
        btn_f.pack(fill=tk.X, side=tk.BOTTOM)
        def on_export():
            chosen = format_var.get()
            do_upload = upload_var.get()
            auth = auth_var.get()
            userhash = None
            if do_upload and auth == "account":
                userhash = userhash_entry.get().strip()
                if not userhash:
                    self.show_alert("Userhash Required", "Please enter your Catbox userhash.")
                    return
            win.destroy()
            self.run_upload_export(chosen, do_upload, userhash)
        def on_cancel():
            win.destroy()
        tk.Button(btn_f, text="Export & Upload", bg="#007acc", fg="white",
                  font=("Arial", 9, "bold"), width=12,
                  relief=tk.FLAT, command=on_export).pack(side=tk.RIGHT, padx=(6,0))
        tk.Button(btn_f, text="Cancel", bg="#444444", fg="white",
                  font=("Arial", 9, "bold"), width=10,
                  relief=tk.FLAT, command=on_cancel).pack(side=tk.RIGHT)
        auth_frame.pack_forget()
        userhash_entry.pack_forget()

    def run_upload_export(self, format_label, do_upload, userhash):
        fmt = self.VIDEO_FORMATS.get(format_label)
        if not fmt:
            self.show_alert("Export Error", f"Unknown video format: {format_label}")
            return
        ext = fmt["ext"]
        path = filedialog.asksaveasfilename(defaultextension=f".{ext}",
                                            filetypes=[(format_label, f"*.{ext}"), ("All Files", "*.*")])
        if not path:
            return
        self.play_sound("printer.wav")
        self.root.config(cursor="watch")
        self.root.update()
        try:
            pil_frames = []
            for frame in self.frames:
                comp = Image.new("RGBA", (self.canvas_width, self.canvas_height), (255, 255, 255, 255))
                for layer in reversed(frame.layers):
                    if layer.visible:
                        comp.alpha_composite(layer.image)
                pil_frames.append(comp.convert("RGB"))
            import numpy as np
            frame_array = [np.array(img) for img in pil_frames]
            clip = mp.ImageSequenceClip(frame_array, fps=self.fps)
            if self.audio_clips:
                audio_clips = []
                for clip_data in self.audio_clips:
                    audio_path = clip_data["path"]
                    if not os.path.exists(audio_path):
                        continue
                    try:
                        audio = mp.AudioFileClip(audio_path)
                        start = clip_data["trim_start"]
                        end = clip_data["duration"] - clip_data["trim_end"]
                        if end > start:
                            audio = audio.subclip(start, end)
                        audio = audio.volumex(clip_data["volume"])
                        audio = audio.set_start(clip_data["start"])
                        audio_clips.append(audio)
                    except:
                        pass
                if audio_clips:
                    final_audio = mp.CompositeAudioClip(audio_clips)
                    if final_audio.duration < clip.duration:
                        silence = mp.AudioClip(lambda t: 0, duration=clip.duration - final_audio.duration)
                        final_audio = mp.CompositeAudioClip([final_audio, silence])
                    clip = clip.set_audio(final_audio)
            codec = fmt.get("codec", "libx264")
            audio_codec = fmt.get("audio_codec", "aac")
            clip.write_videofile(path, codec=codec, audio_codec=audio_codec, fps=self.fps, verbose=False, logger=None)
            self.root.config(cursor="")
            self.show_alert("Export Complete", f"Successfully exported {format_label} video to:\n{path}")
            if do_upload:
                self.root.config(cursor="watch")
                result = upload_file(path, userhash)
                self.root.config(cursor="")
                if result.startswith("http"):
                    self.show_alert("Upload Successful", f"Uploaded to Catbox:\n{result}")
                else:
                    self.show_error_dialog(f"Upload failed: {result}")
        except Exception as e:
            self.root.config(cursor="")
            self.show_error_dialog(f"Export/Upload error:\n{str(e)}")

    # ---------- Export ----------
    def export_video_with_audio(self):
        if not HAS_MOVIEPY:
            if not self.check_ffmpeg_installed():
                return
            self.show_video_format_dialog_fallback()
            return
        self.show_video_format_dialog()

    def show_video_format_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("Export Video")
        win.geometry("380x320")
        win.configure(bg="#2a2a2a")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)
        win.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        win.geometry(f"+{px + (pw // 2) - 190}+{py + (ph // 2) - 160}")
        tk.Label(win, text="Choose a video format to export:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).pack(pady=(15, 8), padx=15, anchor="w")
        if self.audio_clips:
            tk.Label(win, text="🎵 Audio clips detected - will be included!",
                     bg="#2a2a2a", fg="#88ff88", font=("Arial", 9, "bold")).pack(pady=(0, 10))
        else:
            tk.Label(win, text="No audio clips - video only",
                     bg="#2a2a2a", fg="#888888", font=("Arial", 9)).pack(pady=(0, 10))
        format_var = tk.StringVar(value=next(iter(self.VIDEO_FORMATS)))
        list_frame = tk.Frame(win, bg="#2a2a2a")
        list_frame.pack(fill=tk.BOTH, expand=True, padx=15)
        for label in self.VIDEO_FORMATS:
            rb = tk.Radiobutton(list_frame, text=label, variable=format_var, value=label,
                                bg="#2a2a2a", fg="white", selectcolor="#1e1e1e",
                                activebackground="#2a2a2a", activeforeground="white",
                                font=("Arial", 9), anchor="w")
            rb.pack(fill=tk.X, pady=3)
        btn_f = tk.Frame(win, bg="#1e1e1e", pady=10, padx=15)
        btn_f.pack(fill=tk.X, side=tk.BOTTOM)
        def on_export():
            chosen = format_var.get()
            win.destroy()
            self.run_video_export_with_moviepy(chosen)
        def on_cancel():
            win.destroy()
        tk.Button(btn_f, text="Export", bg="#007acc", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=on_export).pack(side=tk.RIGHT, padx=(6,0))
        tk.Button(btn_f, text="Cancel", bg="#444444", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=on_cancel).pack(side=tk.RIGHT)

    def run_video_export_with_moviepy(self, format_label):
        fmt = self.VIDEO_FORMATS.get(format_label)
        if not fmt:
            self.show_alert("Export Error", f"Unknown video format: {format_label}")
            return
        ext = fmt["ext"]
        path = filedialog.asksaveasfilename(defaultextension=f".{ext}",
                                            filetypes=[(format_label, f"*.{ext}"), ("All Files", "*.*")])
        if not path:
            return
        self.play_sound("printer.wav")
        self.root.config(cursor="watch")
        self.root.update()
        try:
            pil_frames = []
            for frame in self.frames:
                comp = Image.new("RGBA", (self.canvas_width, self.canvas_height), (255, 255, 255, 255))
                for layer in reversed(frame.layers):
                    if layer.visible:
                        comp.alpha_composite(layer.image)
                pil_frames.append(comp.convert("RGB"))
            import numpy as np
            frame_array = [np.array(img) for img in pil_frames]
            clip = mp.ImageSequenceClip(frame_array, fps=self.fps)
            if self.audio_clips:
                audio_clips = []
                for clip_data in self.audio_clips:
                    audio_path = clip_data["path"]
                    if not os.path.exists(audio_path):
                        continue
                    try:
                        audio = mp.AudioFileClip(audio_path)
                        start = clip_data["trim_start"]
                        end = clip_data["duration"] - clip_data["trim_end"]
                        if end > start:
                            audio = audio.subclip(start, end)
                        audio = audio.volumex(clip_data["volume"])
                        audio = audio.set_start(clip_data["start"])
                        audio_clips.append(audio)
                    except:
                        pass
                if audio_clips:
                    final_audio = mp.CompositeAudioClip(audio_clips)
                    if final_audio.duration < clip.duration:
                        silence = mp.AudioClip(lambda t: 0, duration=clip.duration - final_audio.duration)
                        final_audio = mp.CompositeAudioClip([final_audio, silence])
                    clip = clip.set_audio(final_audio)
            codec = fmt.get("codec", "libx264")
            audio_codec = fmt.get("audio_codec", "aac")
            clip.write_videofile(path, codec=codec, audio_codec=audio_codec, fps=self.fps, verbose=False, logger=None)
            self.root.config(cursor="")
            self.show_alert("Export Complete", f"Successfully exported {format_label} video to:\n{path}")
        except Exception as e:
            self.root.config(cursor="")
            self.show_error_dialog(f"Export error:\n{str(e)}")

    def show_video_format_dialog_fallback(self):
        win = tk.Toplevel(self.root)
        win.title("Export Video (FFmpeg)")
        win.geometry("380x320")
        win.configure(bg="#2a2a2a")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)
        win.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        win.geometry(f"+{px + (pw // 2) - 190}+{py + (ph // 2) - 160}")
        tk.Label(win, text="Choose a video format (FFmpeg):", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).pack(pady=(15, 8), padx=15, anchor="w")
        if self.audio_clips:
            tk.Label(win, text="🎵 Audio included", bg="#2a2a2a", fg="#88ff88",
                     font=("Arial", 9, "bold")).pack(pady=(0, 10))
        format_var = tk.StringVar(value=next(iter(self.VIDEO_FORMATS)))
        list_frame = tk.Frame(win, bg="#2a2a2a")
        list_frame.pack(fill=tk.BOTH, expand=True, padx=15)
        for label in self.VIDEO_FORMATS:
            rb = tk.Radiobutton(list_frame, text=label, variable=format_var, value=label,
                                bg="#2a2a2a", fg="white", selectcolor="#1e1e1e",
                                activebackground="#2a2a2a", activeforeground="white",
                                font=("Arial", 9), anchor="w")
            rb.pack(fill=tk.X, pady=3)
        btn_f = tk.Frame(win, bg="#1e1e1e", pady=10, padx=15)
        btn_f.pack(fill=tk.X, side=tk.BOTTOM)
        def on_export():
            chosen = format_var.get()
            win.destroy()
            self.run_video_export_with_audio_old(chosen)
        def on_cancel():
            win.destroy()
        tk.Button(btn_f, text="Export", bg="#007acc", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=on_export).pack(side=tk.RIGHT, padx=(6,0))
        tk.Button(btn_f, text="Cancel", bg="#444444", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=on_cancel).pack(side=tk.RIGHT)

    def run_video_export_with_audio_old(self, format_label):
        fmt = self.VIDEO_FORMATS.get(format_label)
        if not fmt:
            self.show_alert("Export Error", f"Unknown video format: {format_label}")
            return
        ext = fmt["ext"]
        path = filedialog.asksaveasfilename(defaultextension=f".{ext}",
                                            filetypes=[(format_label, f"*.{ext}"), ("All Files", "*.*")])
        if not path:
            return
        self.play_sound("printer.wav")
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_video = os.path.join(temp_dir, "video.mp4")
            temp_audio = os.path.join(temp_dir, "audio.wav")
            try:
                video_cmd = [
                    'ffmpeg', '-y',
                    '-f', 'rawvideo',
                    '-vcodec', 'rawvideo',
                    '-s', f'{self.canvas_width}x{self.canvas_height}',
                    '-pix_fmt', 'rgb24',
                    '-r', str(self.fps),
                    '-i', '-',
                    '-c:v', 'libx264',
                    '-pix_fmt', 'yuv420p',
                    temp_video
                ]
                proc = subprocess.Popen(video_cmd, stdin=subprocess.PIPE,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                for frame in self.frames:
                    comp = Image.new("RGBA", (self.canvas_width, self.canvas_height), (255, 255, 255, 255))
                    for layer in reversed(frame.layers):
                        if layer.visible:
                            comp.alpha_composite(layer.image)
                    rgb_img = comp.convert("RGB")
                    proc.stdin.write(rgb_img.tobytes())
                proc.stdin.close()
                proc.wait()
                if proc.returncode != 0:
                    err = proc.stderr.read().decode('utf-8', errors='ignore')
                    self.show_error_dialog(f"Video rendering error:\n{err}")
                    return
                if self.audio_clips:
                    self._render_audio_to_file(temp_audio)
                    combine_cmd = [
                        'ffmpeg', '-y',
                        '-i', temp_video,
                        '-i', temp_audio,
                        '-c:v', 'copy',
                        '-c:a', 'aac',
                        '-map', '0:v:0',
                        '-map', '1:a:0',
                        '-shortest',
                        path
                    ]
                    proc = subprocess.Popen(combine_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                    proc.wait()
                    if proc.returncode != 0:
                        err = proc.stderr.read().decode('utf-8', errors='ignore')
                        self.show_error_dialog(f"Audio mixing error:\n{err}")
                        return
                else:
                    shutil.copy2(temp_video, path)
                self.show_alert("Export Complete",
                    f"Successfully exported {format_label} video to:\n{path}\n"
                    f"{'Audio included!' if self.audio_clips else 'No audio in timeline.'}")
            except Exception as e:
                self.show_error_dialog(f"An error occurred while exporting video:\n{str(e)}")

    def _render_audio_to_file(self, output_path):
        if not self.audio_clips:
            return
        with tempfile.TemporaryDirectory() as temp_dir:
            audio_files = []
            for i, clip in enumerate(self.audio_clips):
                clip_file = os.path.join(temp_dir, f"clip_{i}.wav")
                audio_files.append(clip_file)
                visible_dur = clip["duration"] - clip["trim_start"] - clip["trim_end"]
                if visible_dur <= 0:
                    continue
                cmd = [
                    'ffmpeg', '-y',
                    '-i', clip["path"],
                    '-ss', str(clip["trim_start"]),
                    '-t', str(visible_dur),
                    '-af', f"volume={clip['volume']}",
                    '-acodec', 'pcm_s16le',
                    '-ar', '44100',
                    clip_file
                ]
                proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                proc.wait()
                if proc.returncode != 0:
                    continue
            if audio_files:
                total_duration = 0.0
                for clip in self.audio_clips:
                    clip_end = clip["start"] + clip["duration"] - clip["trim_start"] - clip["trim_end"]
                    total_duration = max(total_duration, clip_end)
                filter_parts = []
                for i, clip in enumerate(self.audio_clips):
                    if i >= len(audio_files):
                        break
                    if not os.path.exists(audio_files[i]):
                        continue
                    visible_dur = clip["duration"] - clip["trim_start"] - clip["trim_end"]
                    if visible_dur <= 0:
                        continue
                    start_time = clip["start"]
                    filter_parts.append(f"[{i}:a]adelay={int(start_time * 1000)}|{int(start_time * 1000)}[a{i}]")
                if filter_parts:
                    cmd = ['ffmpeg', '-y']
                    for afile in audio_files:
                        if os.path.exists(afile):
                            cmd.extend(['-i', afile])
                    filter_str = ';'.join(filter_parts)
                    inputs = ''.join([f'[a{i}]' for i in range(len(audio_files))])
                    filter_str += f';{inputs}amix=inputs={len(audio_files)}[out]'
                    cmd.extend(['-filter_complex', filter_str])
                    cmd.extend(['-map', '[out]'])
                    cmd.extend(['-acodec', 'pcm_s16le', '-ar', '44100'])
                    cmd.append(output_path)
                    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                    proc.wait()
                    if proc.returncode != 0:
                        if audio_files and os.path.exists(audio_files[0]):
                            shutil.copy2(audio_files[0], output_path)

    # ---------- ERASER ----------
    def draw_with_brush(self, x, y, alpha=255):
        if self.current_brush_name == "Pixel Brush":
            self.draw_with_pixel_brush(x, y, alpha)
            return
        if self.current_brush_name == "Pen":
            layer = self.get_active_layer_object()
            if not layer:
                return
            draw = ImageDraw.Draw(layer.image)
            if alpha == 0:
                color = (0, 0, 0, 0)
            else:
                color = self.hex_to_rgba(self.current_color)
            width = max(1, int(self.brush_size))
            radius = width / 2
            if self.last_x is not None and self.last_y is not None:
                draw.line([(self.last_x, self.last_y), (x, y)], fill=color, width=width, joint="round")
                draw.ellipse([x - radius, y - radius, x + radius, y + radius], fill=color)
            else:
                draw.ellipse([x - radius, y - radius, x + radius, y + radius], fill=color)
            self.last_x, self.last_y = x, y
            self.render_canvas()
            return
        layer = self.get_active_layer_object()
        if not layer:
            return
        brush = self.current_brush
        if brush is None:
            return
        base_size = max(brush.width, brush.height)
        scale = self.brush_size / base_size
        new_size = int(base_size * scale)
        if new_size < 1:
            new_size = 1
        if new_size != base_size:
            brush_resized = brush.resize((new_size, new_size), BILINEAR)
        else:
            brush_resized = brush
        brush_data = brush_resized.getdata()
        brush_width, brush_height = brush_resized.size
        paste_x = int(x - brush_width // 2)
        paste_y = int(y - brush_height // 2)
        if alpha == 0:
            erase_img = Image.new("RGBA", (brush_width, brush_height), (0, 0, 0, 0))
            mask = brush_resized.split()[3]
            layer.image.paste(erase_img, (paste_x, paste_y), mask)
        else:
            color = self.hex_to_rgba(self.current_color)
            colored_brush = Image.new("RGBA", (brush_width, brush_height), (0, 0, 0, 0))
            colored_data = []
            for pixel in brush_data:
                if pixel[3] > 0:
                    a = pixel[3] / 255.0
                    colored_data.append((color[0], color[1], color[2], int(a * 255)))
                else:
                    colored_data.append((0, 0, 0, 0))
            colored_brush.putdata(colored_data)
            layer.image.paste(colored_brush, (paste_x, paste_y), colored_brush)
        self.render_canvas()

    def draw_with_pixel_brush(self, x, y, alpha=255):
        layer = self.get_active_layer_object()
        if not layer:
            return
        cell = max(1, int(self.brush_size))
        if alpha == 0:
            color = (0, 0, 0, 0)
        else:
            color = self.hex_to_rgba(self.current_color)
        sx, sy = self.last_x if self.last_x is not None else x, self.last_y if self.last_y is not None else y
        distance = max(abs(x - sx), abs(y - sy), 1)
        steps = max(1, int(distance / max(1, cell // 2)))
        draw = ImageDraw.Draw(layer.image)
        for i in range(steps + 1):
            t = i / steps
            px = int(round(sx + (x - sx) * t))
            py = int(round(sy + (y - sy) * t))
            gx = (px // cell) * cell
            gy = (py // cell) * cell
            draw.rectangle([gx, gy, gx + cell - 1, gy + cell - 1], fill=color)
        self.last_x, self.last_y = x, y
        self.render_canvas()

    def on_draw_start(self, event):
        cx, cy = self.screen_to_canvas_coords(event.x, event.y)
        self.start_x, self.start_y = cx, cy
        self.last_x, self.last_y = cx, cy
        if self.current_tool == "zoom":
            self.zoom_level = min(4.0, self.zoom_level + 0.25)
            self.render_canvas()
            return
        if self.current_tool == "eyedropper":
            self.pick_color(cx, cy)
            return
        if self.current_tool == "text" and self.text_mode:
            self.text_position = (cx, cy)
            self.open_text_control_window()
            self.render_text_preview()
            return
        if self.current_tool == "marquee":
            self.start_marquee_selection(event)
            return
        if self.current_tool == "selection":
            if self.selection_active and self.selected_pixels:
                self.start_selection_drag(event)
            return
        if self.current_tool == "blur":
            self.save_undo_state()
            self.apply_blur(event)
            return
        if self.current_tool == "smudge":
            self.save_undo_state()
            self.apply_smudge(cx, cy)
            return
        if self.current_tool == "eraser":
            self.save_undo_state()
            self.draw_with_brush(cx, cy, alpha=0)
            return
        layer = self.get_active_layer_object()
        if not layer:
            return
        self.save_undo_state()
        if self.current_tool == "pencil":
            self.draw_with_brush(cx, cy)

    def on_draw_motion(self, event):
        cx, cy = self.screen_to_canvas_coords(event.x, event.y)
        if self.current_tool == "pencil":
            self.draw_with_brush(cx, cy)
        elif self.current_tool == "eraser":
            self.draw_with_brush(cx, cy, alpha=0)
        elif self.current_tool == "smudge":
            self.apply_smudge(cx, cy)
        elif self.current_tool == "marquee":
            self.update_marquee_selection(event)
        elif self.current_tool == "selection":
            if self.is_dragging_selection:
                self.drag_selection(event)
        elif self.current_tool == "blur":
            self.apply_blur(event)
        elif self.current_tool == "shape":
            if self.preview_shape_id:
                self.canvas.delete(self.preview_shape_id)
            sx = self.start_x * self.zoom_level + self.img_top_left_x
            sy = self.start_y * self.zoom_level + self.img_top_left_y
            ex = cx * self.zoom_level + self.img_top_left_x
            ey = cy * self.zoom_level + self.img_top_left_y
            self.preview_shape_id = self.canvas.create_rectangle(sx, sy, ex, ey, outline=self.current_color, width=2, dash=(4, 4))

    def on_draw_stop(self, event):
        cx, cy = self.screen_to_canvas_coords(event.x, event.y)
        if self.preview_shape_id:
            self.canvas.delete(self.preview_shape_id)
            self.preview_shape_id = None
        if self.current_tool == "marquee":
            self.finish_marquee_selection(event)
            return
        if self.current_tool == "selection":
            if self.is_dragging_selection:
                self.finish_selection_drag(event)
            return
        if self.current_tool == "eraser":
            return
        layer = self.get_active_layer_object()
        if not layer:
            return
        draw = ImageDraw.Draw(layer.image)
        rgba = self.hex_to_rgba(self.current_color)
        if self.current_tool == "shape":
            x0, y0 = min(self.start_x, cx), min(self.start_y, cy)
            x1, y1 = max(self.start_x, cx), max(self.start_y, cy)
            draw.rectangle([x0, y0, x1, y1], outline=rgba, width=self.brush_size)
            self.render_canvas()

    # ---------- TEXT TOOL ----------
    def open_text_control_window(self):
        if self.text_control_window is not None and self.text_control_window.winfo_exists():
            self.text_control_window.lift()
            return
        self.text_control_window = tk.Toplevel(self.root)
        self.text_control_window.title("Text Controls")
        self.text_control_window.geometry("400x340")
        self.text_control_window.configure(bg="#2a2a2a")
        self.text_control_window.transient(self.root)
        self.text_control_window.grab_set()
        self.text_control_window.resizable(False, False)
        self.text_control_window.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        self.text_control_window.geometry(f"+{px + (pw // 2) - 200}+{py + (ph // 2) - 170}")
        tk.Label(self.text_control_window, text="Font:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).grid(row=0, column=0, padx=10, pady=10, sticky="w")
        import tkinter.font as tkfont
        font_list = sorted(tkfont.families())
        self.font_var = tk.StringVar(value=self.text_font)
        font_dropdown = ttk.Combobox(self.text_control_window, textvariable=self.font_var,
                                     values=font_list, width=25, state="readonly")
        font_dropdown.grid(row=0, column=1, padx=10, pady=10, sticky="w")
        font_dropdown.bind("<<ComboboxSelected>>", lambda e: self.update_text_font())
        tk.Label(self.text_control_window, text="Size:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).grid(row=1, column=0, padx=10, pady=5, sticky="w")
        self.size_var = tk.IntVar(value=self.text_size)
        size_spinbox = tk.Spinbox(self.text_control_window, from_=8, to=200, width=8,
                                  textvariable=self.size_var, bg="#333", fg="white",
                                  relief=tk.FLAT, command=self.update_text_size)
        size_spinbox.grid(row=1, column=1, padx=10, pady=5, sticky="w")
        style_frame = tk.Frame(self.text_control_window, bg="#2a2a2a")
        style_frame.grid(row=2, column=0, columnspan=2, padx=10, pady=10, sticky="w")
        self.bold_btn = tk.Button(style_frame, text="B", font=("Arial", 10, "bold"),
                                  bg="#444" if not self.text_bold else "#007acc", fg="white",
                                  width=3, relief=tk.FLAT, command=self.toggle_bold)
        self.bold_btn.pack(side=tk.LEFT, padx=2)
        self.italic_btn = tk.Button(style_frame, text="I", font=("Arial", 10, "italic"),
                                    bg="#444" if not self.text_italic else "#007acc", fg="white",
                                    width=3, relief=tk.FLAT, command=self.toggle_italic)
        self.italic_btn.pack(side=tk.LEFT, padx=2)
        self.underline_btn = tk.Button(style_frame, text="U", font=("Arial", 10, "underline"),
                                       bg="#444" if not self.text_underline else "#007acc", fg="white",
                                       width=3, relief=tk.FLAT, command=self.toggle_underline)
        self.underline_btn.pack(side=tk.LEFT, padx=2)
        self.strike_btn = tk.Button(style_frame, text="S", font=("Arial", 10, "overstrike"),
                                    bg="#444" if not self.text_strikethrough else "#007acc", fg="white",
                                    width=3, relief=tk.FLAT, command=self.toggle_strikethrough)
        self.strike_btn.pack(side=tk.LEFT, padx=2)
        tk.Label(self.text_control_window, text="Text:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).grid(row=3, column=0, padx=10, pady=5, sticky="nw")
        text_frame = tk.Frame(self.text_control_window, bg="#333")
        text_frame.grid(row=3, column=1, padx=10, pady=5, sticky="w")
        self.text_entry = tk.Text(text_frame, width=25, height=5, bg="#333", fg="white",
                                  insertbackground="white", relief=tk.FLAT, wrap=tk.WORD)
        self.text_entry.pack()
        self.text_entry.insert("1.0", self.text_string)
        self.text_entry.bind("<KeyRelease>", self.update_text_string)
        color_frame = tk.Frame(self.text_control_window, bg="#2a2a2a")
        color_frame.grid(row=4, column=0, columnspan=2, padx=10, pady=10, sticky="w")
        tk.Label(color_frame, text="Color:", bg="#2a2a2a", fg="white",
                 font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(0, 10))
        self.color_preview_btn = tk.Button(color_frame, bg=self.current_color, width=6, height=1,
                                           relief=tk.RAISED, command=self.pick_text_color)
        self.color_preview_btn.pack(side=tk.LEFT)
        btn_frame = tk.Frame(self.text_control_window, bg="#2a2a2a")
        btn_frame.grid(row=5, column=0, columnspan=2, padx=10, pady=15)
        tk.Button(btn_frame, text="✓ Done", bg="#007acc", fg="white",
                  font=("Arial", 10, "bold"), padx=30, pady=8,
                  relief=tk.FLAT, command=self.apply_text).pack(side=tk.LEFT, padx=5)
        tk.Button(btn_frame, text="✕ Cancel", bg="#555", fg="white",
                  font=("Arial", 10, "bold"), padx=20, pady=8,
                  relief=tk.FLAT, command=self.cancel_text).pack(side=tk.LEFT, padx=5)
        self.text_entry.focus_set()

    def pick_text_color(self):
        color = colorchooser.askcolor(title="Choose Text Color", color=self.current_color)
        if color and color[1]:
            self.current_color = color[1]
            self.color_preview_btn.config(bg=self.current_color)
            if self.text_mode and self.text_string:
                self.render_text_preview()

    def update_text_font(self):
        self.text_font = self.font_var.get()
        if self.text_mode and self.text_string:
            self.render_text_preview()

    def update_text_size(self):
        try:
            self.text_size = self.size_var.get()
            if self.text_mode and self.text_string:
                self.render_text_preview()
        except:
            pass

    def toggle_bold(self):
        self.text_bold = not self.text_bold
        self.bold_btn.config(bg="#007acc" if self.text_bold else "#444")
        if self.text_mode and self.text_string:
            self.render_text_preview()

    def toggle_italic(self):
        self.text_italic = not self.text_italic
        self.italic_btn.config(bg="#007acc" if self.text_italic else "#444")
        if self.text_mode and self.text_string:
            self.render_text_preview()

    def toggle_underline(self):
        self.text_underline = not self.text_underline
        self.underline_btn.config(bg="#007acc" if self.text_underline else "#444")
        if self.text_mode and self.text_string:
            self.render_text_preview()

    def toggle_strikethrough(self):
        self.text_strikethrough = not self.text_strikethrough
        self.strike_btn.config(bg="#007acc" if self.text_strikethrough else "#444")
        if self.text_mode and self.text_string:
            self.render_text_preview()

    def update_text_string(self, event=None):
        self.text_string = self.text_entry.get("1.0", tk.END).strip()
        if self.text_mode and self.text_string:
            self.render_text_preview()

    def render_text_preview(self):
        if not self.text_mode or not self.text_string:
            self.clear_text_gizmos()
            self.render_canvas()
            return
        self.clear_text_gizmos()
        layer = self.get_active_layer_object()
        if not layer:
            return
        try:
            font = ImageFont.truetype(self.text_font + ".ttf", self.text_size)
        except:
            try:
                font = ImageFont.truetype("arial.ttf", self.text_size)
            except:
                font = ImageFont.load_default()
        temp_img = Image.new("RGBA", (1, 1), (0, 0, 0, 0))
        temp_draw = ImageDraw.Draw(temp_img)
        bbox = temp_draw.textbbox((0, 0), self.text_string, font=font)
        text_width = bbox[2] - bbox[0]
        text_height = bbox[3] - bbox[1]
        x, y = self.text_position
        if self.text_info:
            old_x = self.text_info.get("x", x)
            old_y = self.text_info.get("y", y)
            old_w = self.text_info.get("width", text_width) + 10
            old_h = self.text_info.get("height", text_height) + 10
            draw = ImageDraw.Draw(layer.image)
            draw.rectangle([old_x - 5, old_y - 5, old_x + old_w + 5, old_y + old_h + 5], fill=(0, 0, 0, 0))
        draw = ImageDraw.Draw(layer.image)
        rgba = self.hex_to_rgba(self.current_color)
        if self.text_underline:
            underline_y = y + text_height + 2
            draw.line([(x, underline_y), (x + text_width, underline_y)], fill=rgba, width=2)
        if self.text_strikethrough:
            strike_y = y + text_height // 2
            draw.line([(x, strike_y), (x + text_width, strike_y)], fill=rgba, width=2)
        draw.text((x, y), self.text_string, fill=rgba, font=font)
        self.text_info = {
            "x": x, "y": y, "width": text_width, "height": text_height,
            "font": font, "text": self.text_string, "color": rgba, "size": self.text_size
        }
        self.draw_text_gizmos(x, y, text_width, text_height)
        self.render_canvas()

    def draw_text_gizmos(self, x, y, width, height):
        self.clear_text_gizmos()
        sx = x * self.zoom_level + self.img_top_left_x
        sy = y * self.zoom_level + self.img_top_left_y
        sw = width * self.zoom_level
        sh = height * self.zoom_level
        self.text_gizmo_ids.append(
            self.canvas.create_rectangle(sx - 5, sy - 5, sx + sw + 5, sy + sh + 5,
                                         outline="#00ff00", dash=(4, 4), width=1.5)
        )
        handle_size = 8
        handles = [
            (sx - 5, sy - 5), (sx + sw + 5, sy - 5),
            (sx - 5, sy + sh + 5), (sx + sw + 5, sy + sh + 5)
        ]
        for hx, hy in handles:
            self.text_gizmo_ids.append(
                self.canvas.create_rectangle(hx - handle_size//2, hy - handle_size//2,
                                            hx + handle_size//2, hy + handle_size//2,
                                            fill="#00ff00" if not self.text_scale_mode else "#ff8800",
                                            outline="#ffffff", width=1)
            )
        if not self.text_scale_mode:
            arrow_size = 10
            self.text_gizmo_ids.append(
                self.canvas.create_polygon(sx + sw//2, sy - 15 - arrow_size,
                                          sx + sw//2 - arrow_size//2, sy - 15,
                                          sx + sw//2 + arrow_size//2, sy - 15,
                                          fill="#00ff00", outline="#ffffff")
            )
            self.text_gizmo_ids.append(
                self.canvas.create_polygon(sx + sw//2, sy + sh + 15 + arrow_size,
                                          sx + sw//2 - arrow_size//2, sy + sh + 15,
                                          sx + sw//2 + arrow_size//2, sy + sh + 15,
                                          fill="#00ff00", outline="#ffffff")
            )
            self.text_gizmo_ids.append(
                self.canvas.create_polygon(sx - 15 - arrow_size, sy + sh//2,
                                          sx - 15, sy + sh//2 - arrow_size//2,
                                          sx - 15, sy + sh//2 + arrow_size//2,
                                          fill="#00ff00", outline="#ffffff")
            )
            self.text_gizmo_ids.append(
                self.canvas.create_polygon(sx + sw + 15 + arrow_size, sy + sh//2,
                                          sx + sw + 15, sy + sh//2 - arrow_size//2,
                                          sx + sw + 15, sy + sh//2 + arrow_size//2,
                                          fill="#00ff00", outline="#ffffff")
            )
        else:
            side_size = 8
            self.text_gizmo_ids.append(
                self.canvas.create_rectangle(sx + sw//2 - side_size//2, sy - 10,
                                            sx + sw//2 + side_size//2, sy + 2,
                                            fill="#ff8800", outline="#ffffff")
            )
            self.text_gizmo_ids.append(
                self.canvas.create_rectangle(sx + sw//2 - side_size//2, sy + sh - 2,
                                            sx + sw//2 + side_size//2, sy + sh + 10,
                                            fill="#ff8800", outline="#ffffff")
            )
            self.text_gizmo_ids.append(
                self.canvas.create_rectangle(sx - 10, sy + sh//2 - side_size//2,
                                            sx + 2, sy + sh//2 + side_size//2,
                                            fill="#ff8800", outline="#ffffff")
            )
            self.text_gizmo_ids.append(
                self.canvas.create_rectangle(sx + sw - 2, sy + sh//2 - side_size//2,
                                            sx + sw + 10, sy + sh//2 + side_size//2,
                                            fill="#ff8800", outline="#ffffff")
            )
        for gid in self.text_gizmo_ids:
            self.canvas.tag_bind(gid, "<ButtonPress-1>", self.on_gizmo_press)
            self.canvas.tag_bind(gid, "<B1-Motion>", self.on_gizmo_drag)
            self.canvas.tag_bind(gid, "<ButtonRelease-1>", self.on_gizmo_release)

    def clear_text_gizmos(self):
        for gid in self.text_gizmo_ids:
            try: self.canvas.delete(gid)
            except: pass
        self.text_gizmo_ids = []

    def on_gizmo_press(self, event):
        if not self.text_mode or not self.text_info:
            return
        self.text_drag_start = (event.x, event.y)
        self.text_original_bbox = self.text_info.copy()
        x, y = self.text_position
        sx = x * self.zoom_level + self.img_top_left_x
        sy = y * self.zoom_level + self.img_top_left_y
        sw = self.text_info["width"] * self.zoom_level
        sh = self.text_info["height"] * self.zoom_level
        handle_size = 8
        corners = [
            (sx - 5, sy - 5), (sx + sw + 5, sy - 5),
            (sx - 5, sy + sh + 5), (sx + sw + 5, sy + sh + 5)
        ]
        self.text_drag_type = "move"
        for hx, hy in corners:
            if abs(event.x - hx) < 10 and abs(event.y - hy) < 10:
                self.text_drag_type = "scale_corner"
                break
        if self.text_drag_type == "move":
            if abs(event.x - (sx + sw//2)) < 15 and abs(event.y - (sy - 10)) < 10:
                self.text_drag_type = "scale_up"
            elif abs(event.x - (sx + sw//2)) < 15 and abs(event.y - (sy + sh + 10)) < 10:
                self.text_drag_type = "scale_down"
            elif abs(event.x - (sx - 10)) < 10 and abs(event.y - (sy + sh//2)) < 15:
                self.text_drag_type = "scale_left"
            elif abs(event.x - (sx + sw + 10)) < 10 and abs(event.y - (sy + sh//2)) < 15:
                self.text_drag_type = "scale_right"
        if self.text_drag_type == "move":
            arrow_size = 10
            if abs(event.x - (sx + sw//2)) < arrow_size and abs(event.y - (sy - 15 - arrow_size//2)) < arrow_size:
                self.text_drag_type = "move_up"
            elif abs(event.x - (sx + sw//2)) < arrow_size and abs(event.y - (sy + sh + 15 + arrow_size//2)) < arrow_size:
                self.text_drag_type = "move_down"
            elif abs(event.x - (sx - 15 - arrow_size//2)) < arrow_size and abs(event.y - (sy + sh//2)) < arrow_size:
                self.text_drag_type = "move_left"
            elif abs(event.x - (sx + sw + 15 + arrow_size//2)) < arrow_size and abs(event.y - (sy + sh//2)) < arrow_size:
                self.text_drag_type = "move_right"

    def on_gizmo_drag(self, event):
        if not self.text_mode or not self.text_drag_start or not self.text_original_bbox or not self.text_info:
            return
        dx = event.x - self.text_drag_start[0]
        dy = event.y - self.text_drag_start[1]
        if self.text_drag_type in ["move", "move_up", "move_down", "move_left", "move_right"]:
            new_x = self.text_original_bbox["x"]
            new_y = self.text_original_bbox["y"]
            if self.text_drag_type == "move":
                new_x += dx / self.zoom_level
                new_y += dy / self.zoom_level
            elif self.text_drag_type == "move_up":
                new_y += dy / self.zoom_level
            elif self.text_drag_type == "move_down":
                new_y += dy / self.zoom_level
            elif self.text_drag_type == "move_left":
                new_x += dx / self.zoom_level
            elif self.text_drag_type == "move_right":
                new_x += dx / self.zoom_level
            self.text_position = (max(0, new_x), max(0, new_y))
            self.render_text_preview()
        elif self.text_drag_type in ["scale_corner", "scale_up", "scale_down", "scale_left", "scale_right"]:
            if self.text_drag_type == "scale_corner":
                new_size = max(8, self.text_original_bbox["size"] + (dx + dy) / 3)
            elif self.text_drag_type == "scale_up":
                new_size = max(8, self.text_original_bbox["size"] - dy / 2)
            elif self.text_drag_type == "scale_down":
                new_size = max(8, self.text_original_bbox["size"] + dy / 2)
            elif self.text_drag_type == "scale_left":
                new_size = max(8, self.text_original_bbox["size"] - dx / 2)
            elif self.text_drag_type == "scale_right":
                new_size = max(8, self.text_original_bbox["size"] + dx / 2)
            self.text_size = int(new_size)
            self.size_var.set(self.text_size)
            self.render_text_preview()

    def on_gizmo_release(self, event):
        self.text_drag_start = None
        self.text_original_bbox = None

    def apply_text(self):
        if not self.text_mode:
            return
        self.save_undo_state()
        self.text_applied = True
        self.exit_text_mode()
        if self.text_control_window is not None:
            try: self.text_control_window.destroy()
            except: pass
            self.text_control_window = None
        self.render_canvas()

    def exit_text_mode(self):
        self.text_mode = False
        self.clear_text_gizmos()
        self.text_string = ""
        self.text_info = None
        if not self.text_applied:
            if self.text_info:
                layer = self.get_active_layer_object()
                if layer:
                    x = self.text_info["x"]
                    y = self.text_info["y"]
                    w = self.text_info["width"] + 10
                    h = self.text_info["height"] + 10
                    draw = ImageDraw.Draw(layer.image)
                    draw.rectangle([x - 5, y - 5, x + w + 5, y + h + 5], fill=(0, 0, 0, 0))
        self.text_applied = False
        self.render_canvas()

    def cancel_text(self):
        self.text_applied = False
        if self.text_info:
            layer = self.get_active_layer_object()
            if layer:
                x = self.text_info["x"]
                y = self.text_info["y"]
                w = self.text_info["width"] + 10
                h = self.text_info["height"] + 10
                draw = ImageDraw.Draw(layer.image)
                draw.rectangle([x - 5, y - 5, x + w + 5, y + h + 5], fill=(0, 0, 0, 0))
        self.exit_text_mode()
        if self.text_control_window is not None:
            try: self.text_control_window.destroy()
            except: pass
            self.text_control_window = None
        self.render_canvas()

    # ---------- SELECTION ----------
    def start_marquee_selection(self, event):
        self.clear_selection()
        self.selection_start = (self.start_x, self.start_y)
        self.selection_end = (self.start_x, self.start_y)
        self.is_dragging_selection = False
        self.selection_active = False

    def update_marquee_selection(self, event):
        if self.selection_start:
            cx, cy = self.start_x, self.start_y
            ex, ey = self.screen_to_canvas_coords(event.x, event.y)
            sx = cx * self.zoom_level + self.img_top_left_x
            sy = cy * self.zoom_level + self.img_top_left_y
            ex_s = ex * self.zoom_level + self.img_top_left_x
            ey_s = ey * self.zoom_level + self.img_top_left_y
            if self.selection_rect:
                self.canvas.delete(self.selection_rect)
            self.selection_rect = self.canvas.create_rectangle(
                sx, sy, ex_s, ey_s,
                outline="#00ff00", width=1.5, dash=(4, 4)
            )

    def finish_marquee_selection(self, event):
        if not self.selection_start:
            return
        x0, y0 = self.selection_start
        cx, cy = self.screen_to_canvas_coords(event.x, event.y)
        x1, y1 = cx, cy
        x0, x1 = min(x0, x1), max(x0, x1)
        y0, y1 = min(y0, y1), max(y0, y1)
        layer = self.get_active_layer_object()
        if not layer:
            return
        img = layer.image
        self.selected_pixels = img.crop((x0, y0, x1, y1))
        self.selection_active = True
        self.selection_start = (x0, y0)
        self.selection_end = (x1, y1)
        self.selection_original_position = (x0, y0)
        self.is_dragging_selection = False
        if self.selection_rect:
            self.canvas.delete(self.selection_rect)
        self.selection_rect = self.canvas.create_rectangle(
            x0 * self.zoom_level + self.img_top_left_x,
            y0 * self.zoom_level + self.img_top_left_y,
            x1 * self.zoom_level + self.img_top_left_x,
            y1 * self.zoom_level + self.img_top_left_y,
            outline="#00ff00", width=2
        )

    def start_selection_drag(self, event):
        if not self.selection_active or self.selected_pixels is None:
            return
        cx, cy = self.screen_to_canvas_coords(event.x, event.y)
        x0, y0 = self.selection_start
        x1, y1 = self.selection_end
        if x0 <= cx <= x1 and y0 <= cy <= y1:
            self.is_dragging_selection = True
            self.selection_offset = (cx - x0, cy - y0)

    def drag_selection(self, event):
        if not self.is_dragging_selection or self.selected_pixels is None:
            return
        cx, cy = self.screen_to_canvas_coords(event.x, event.y)
        new_x = cx - self.selection_offset[0]
        new_y = cy - self.selection_offset[1]
        w = self.selection_end[0] - self.selection_start[0]
        h = self.selection_end[1] - self.selection_start[1]
        self.selection_start = (new_x, new_y)
        self.selection_end = (new_x + w, new_y + h)
        if self.selection_rect:
            self.canvas.delete(self.selection_rect)
        self.selection_rect = self.canvas.create_rectangle(
            new_x * self.zoom_level + self.img_top_left_x,
            new_y * self.zoom_level + self.img_top_left_y,
            (new_x + w) * self.zoom_level + self.img_top_left_x,
            (new_y + h) * self.zoom_level + self.img_top_left_y,
            outline="#00ff00", width=2
        )

    def finish_selection_drag(self, event):
        if not self.is_dragging_selection or self.selected_pixels is None:
            return
        self.is_dragging_selection = False
        layer = self.get_active_layer_object()
        if not layer:
            return
        self.save_undo_state()
        x0, y0 = self.selection_start
        x1, y1 = self.selection_end
        w = x1 - x0
        h = y1 - y0
        old_x0, old_y0 = self.selection_original_position
        old_x1 = old_x0 + w
        old_y1 = old_y0 + h
        draw = ImageDraw.Draw(layer.image)
        if old_x0 != x0 or old_y0 != y0:
            draw.rectangle([old_x0, old_y0, old_x1, old_y1], fill=(0, 0, 0, 0))
        draw.rectangle([x0, y0, x1, y1], fill=(0, 0, 0, 0))
        layer.image.paste(self.selected_pixels, (int(x0), int(y0)))
        self.selection_original_position = (x0, y0)
        if self.selection_rect:
            self.canvas.delete(self.selection_rect)
        self.selection_rect = self.canvas.create_rectangle(
            x0 * self.zoom_level + self.img_top_left_x,
            y0 * self.zoom_level + self.img_top_left_y,
            x1 * self.zoom_level + self.img_top_left_x,
            y1 * self.zoom_level + self.img_top_left_y,
            outline="#00ff00", width=2
        )
        self.render_canvas()

    def clear_selection(self):
        if self.selection_rect:
            self.canvas.delete(self.selection_rect)
            self.selection_rect = None
        self.selection_active = False
        self.selected_pixels = None
        self.selection_start = None
        self.selection_end = None
        self.selection_original_position = None
        self.is_dragging_selection = False

    # ---------- BLUR AND SMUDGE ----------
    def apply_blur(self, event):
        layer = self.get_active_layer_object()
        if not layer:
            return
        cx, cy = self.screen_to_canvas_coords(event.x, event.y)
        radius = self.blur_radius
        x0 = max(0, cx - radius)
        y0 = max(0, cy - radius)
        x1 = min(self.canvas_width, cx + radius)
        y1 = min(self.canvas_height, cy + radius)
        region = layer.image.crop((x0, y0, x1, y1))
        blurred = region.filter(ImageFilter.GaussianBlur(radius=radius * 0.5))
        layer.image.paste(blurred, (int(x0), int(y0)))
        self.render_canvas()

    def apply_smudge(self, x, y):
        layer = self.get_active_layer_object()
        if not layer or self.last_x is None or self.last_y is None:
            return
        dx = int(x - self.last_x)
        dy = int(y - self.last_y)
        if dx == 0 and dy == 0:
            return
        radius = max(2, int(self.brush_size) // 2)
        src_box = (
            max(0, int(self.last_x - radius)),
            max(0, int(self.last_y - radius)),
            min(self.canvas_width, int(self.last_x + radius + 1)),
            min(self.canvas_height, int(self.last_y + radius + 1))
        )
        if src_box[2] <= src_box[0] or src_box[3] <= src_box[1]:
            self.last_x, self.last_y = x, y
            return
        source = layer.image.crop(src_box)
        dest_x = src_box[0] + dx
        dest_y = src_box[1] + dy
        mask = Image.new("L", source.size, 0)
        md = ImageDraw.Draw(mask)
        md.ellipse([1, 1, max(1, source.width - 2), max(1, source.height - 2)],
                   fill=int(255 * self.smudge_strength))
        left = max(0, dest_x)
        top = max(0, dest_y)
        right = min(self.canvas_width, dest_x + source.width)
        bottom = min(self.canvas_height, dest_y + source.height)
        if right > left and bottom > top:
            crop_left = left - dest_x
            crop_top = top - dest_y
            crop_right = crop_left + (right - left)
            crop_bottom = crop_top + (bottom - top)
            patch = source.crop((crop_left, crop_top, crop_right, crop_bottom))
            patch_mask = mask.crop((crop_left, crop_top, crop_right, crop_bottom))
            layer.image.paste(patch, (left, top), patch_mask)
        self.last_x, self.last_y = x, y
        self.render_canvas()

    # ---------- CREDITS / HOWTO WITH WORKING SCRUBBER ----------
    def open_credits(self, video_filename="credits.mp4", window_title="Credits", show_scrubber=False):
        if self._credits_window is not None and self._credits_window.winfo_exists():
            self._credits_window.lift()
            return
        video_path = resource_path(os.path.join("video", video_filename))
        if not os.path.isfile(video_path):
            self.show_error_dialog(f"Video not found:\n{video_path}")
            return
        try:
            self.play_sound("click.mp3")
            win = tk.Toplevel(self.root)
            self._credits_window = win
            win.title(f"Freenimate - {window_title}")
            win.configure(bg="black")
            win.geometry("960x540")
            win.minsize(480, 270)
            win.transient(self.root)

            # Main video label
            video_label = tk.Label(win, bg="black")
            video_label.pack(fill=tk.BOTH, expand=True)
            self._credits_video_label = video_label

            # Scrubber area (only for How To)
            self._show_scrubber = show_scrubber
            self._scrubber_frame = None
            self._scrubber = None
            self._time_label = None
            self._video_duration = None
            self._credits_start_time = None
            self._scrubber_dragging = False
            self._current_time = 0.0
            self._last_seek_time = 0.0  # for debounce

            if show_scrubber:
                # Get video duration
                duration = self._get_video_duration(video_path)
                if duration is None:
                    duration = 60.0  # fallback
                self._video_duration = duration

                scrubber_frame = tk.Frame(win, bg="#2a2a2a", height=40)
                scrubber_frame.pack(fill=tk.X, side=tk.BOTTOM, padx=5, pady=5)
                self._scrubber_frame = scrubber_frame

                # Time label
                self._time_label = tk.Label(scrubber_frame, text="0:00 / 0:00", bg="#2a2a2a", fg="white",
                                            font=("Arial", 9))
                self._time_label.pack(side=tk.LEFT, padx=5)

                # Slider
                self._scrubber = tk.Scale(scrubber_frame, from_=0, to=100, orient=tk.HORIZONTAL,
                                         bg="#2a2a2a", fg="white", highlightthickness=0,
                                         troughcolor="#444", sliderlength=12, length=400,
                                         showvalue=0)
                self._scrubber.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)

                # Bind events
                self._scrubber.bind("<ButtonPress-1>", self._on_scrubber_press)
                self._scrubber.bind("<B1-Motion>", self._on_scrubber_drag)
                self._scrubber.bind("<ButtonRelease-1>", self._on_scrubber_release)

                # Initialize time display
                self._update_time_label(0.0)

            self._credits_stop.clear()
            self._credits_queue = queue.Queue(maxsize=3)

            # Launch ffmpeg with -re (real-time) and loop
            cmd = [
                "ffmpeg", "-hide_banner", "-loglevel", "error",
                "-re", "-stream_loop", "-1", "-i", video_path,
                "-f", "image2pipe", "-vcodec", "mjpeg", "-q:v", "5", "-"
            ]
            self._credits_process = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                bufsize=0
            )

            # Audio (optional)
            if HAS_PYGAME:
                try:
                    fd, wav_path = tempfile.mkstemp(suffix=".wav", prefix="freenimate_credits_")
                    os.close(fd)
                    subprocess.run(
                        ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
                         "-i", video_path, "-vn", "-ac", "2", "-ar", "44100", wav_path],
                        check=True
                    )
                    self._credits_audio = (wav_path, pygame.mixer.Sound(wav_path))
                    self._credits_audio[1].play(loops=-1)
                except:
                    self._credits_audio = None

            self._video_path = video_path
            self._credits_start_time = time.time()
            self._current_time = 0.0
            self._last_seek_time = 0.0

            # Start decode thread
            threading.Thread(target=self._credits_decode_loop, daemon=True).start()
            win.protocol("WM_DELETE_WINDOW", self.close_credits)
            win.bind("<Escape>", lambda e: self.close_credits())
            win.bind("<Configure>", self._credits_resize)
            self._credits_last_size = (0, 0)
            self.root.after(10, self._credits_display_loop)

        except Exception as e:
            self.close_credits()
            self.show_error_dialog(f"Failed to open credits video:\n{str(e)}")

    def _get_video_duration(self, video_path):
        if not shutil.which("ffprobe"):
            return None
        try:
            result = subprocess.run(
                ["ffprobe", "-v", "error", "-show_entries", "format=duration",
                 "-of", "csv=p=0", video_path],
                capture_output=True, text=True, timeout=5
            )
            dur = float(result.stdout.strip())
            return dur
        except:
            return None

    def _update_time_label(self, time_sec):
        if self._time_label is None or self._video_duration is None:
            return
        total_sec = self._video_duration
        minutes = int(time_sec // 60)
        seconds = int(time_sec % 60)
        total_minutes = int(total_sec // 60)
        total_seconds = int(total_sec % 60)
        self._time_label.config(text=f"{minutes}:{seconds:02d} / {total_minutes}:{total_seconds:02d}")

    def _on_scrubber_press(self, event):
        self._scrubber_dragging = True

    def _on_scrubber_drag(self, event):
        if self._video_duration is None:
            return
        value = float(self._scrubber.get()) / 100.0
        pos = value * self._video_duration
        self._current_time = pos
        self._update_time_label(pos)
        # Seek only if position changed significantly (debounce ~0.3s)
        if abs(pos - self._last_seek_time) > 0.3:
            self._last_seek_time = pos
            # Do not restart audio during drag (too choppy)
            self._seek_video(pos, restart_audio=False)

    def _on_scrubber_release(self, event):
        self._scrubber_dragging = False
        if self._video_duration is None:
            return
        value = float(self._scrubber.get()) / 100.0
        pos = value * self._video_duration
        self._seek_video(pos, restart_audio=True)

    def _seek_video(self, time_sec, restart_audio=True):
        """Restart ffmpeg with a new seek position and optionally restart audio."""
        if not self._video_path:
            return
        # Stop current process
        self._credits_stop.set()
        if self._credits_process:
            try:
                self._credits_process.kill()
            except:
                pass
            self._credits_process = None
        # Clear queue
        while not self._credits_queue.empty():
            try:
                self._credits_queue.get_nowait()
            except:
                break
        self._credits_stop.clear()

        # Restart with new seek
        seek_time = max(0, min(time_sec, self._video_duration - 1))
        cmd = [
            "ffmpeg", "-hide_banner", "-loglevel", "error",
            "-ss", str(seek_time),
            "-re", "-stream_loop", "-1", "-i", self._video_path,
            "-f", "image2pipe", "-vcodec", "mjpeg", "-q:v", "5", "-"
        ]
        try:
            self._credits_process = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                bufsize=0
            )
            # Restart audio only if requested (on release)
            if restart_audio and HAS_PYGAME and self._credits_audio:
                try:
                    self._credits_audio[1].stop()
                    self._credits_audio[1].play(loops=-1)
                except:
                    pass
            # Reset start time for scrubber tracking
            self._credits_start_time = time.time() - seek_time
            self._current_time = seek_time
            self._update_time_label(seek_time)
            # Update slider to match
            self._scrubber.set((seek_time / self._video_duration) * 100)
        except Exception as e:
            print(f"Seek error: {e}")

    def _credits_decode_loop(self):
        from PIL import Image
        try:
            while not self._credits_stop.is_set() and self._credits_process:
                data = self._credits_read_jpeg()
                if not data:
                    break
                try:
                    img = Image.open(io.BytesIO(data)).convert("RGB")
                    while not self._credits_stop.is_set():
                        try:
                            self._credits_queue.put(img, timeout=0.1)
                            break
                        except queue.Full:
                            try: self._credits_queue.get_nowait()
                            except queue.Empty: pass
                except Exception:
                    continue
        except:
            pass

    def _credits_read_jpeg(self):
        proc = self._credits_process
        if not proc or not proc.stdout:
            return None
        buf = bytearray()
        while not self._credits_stop.is_set():
            chunk = proc.stdout.read(4096)
            if not chunk:
                return None
            buf.extend(chunk)
            end = buf.find(b"\xff\xd9")
            if end != -1:
                return bytes(buf[:end+2])
        return None

    def _credits_display_loop(self):
        win = self._credits_window
        if not win or not win.winfo_exists() or self._credits_stop.is_set():
            return
        try:
            img = None
            while True:
                try:
                    img = self._credits_queue.get_nowait()
                except queue.Empty:
                    break
            if img is not None:
                # Scale image to fill label while preserving aspect ratio
                label_w = max(1, self._credits_video_label.winfo_width())
                label_h = max(1, self._credits_video_label.winfo_height())
                img_copy = img.copy()
                img_copy.thumbnail((label_w, label_h), BILINEAR)
                photo = ImageTk.PhotoImage(img_copy)
                self._credits_photo = photo
                self._credits_video_label.configure(image=photo)

                # Update scrubber if not dragging
                if self._show_scrubber and self._scrubber is not None and not self._scrubber_dragging:
                    # Calculate current position based on elapsed time
                    if self._credits_start_time is not None and self._video_duration is not None:
                        elapsed = time.time() - self._credits_start_time
                        # Modulo for looping
                        if self._video_duration > 0:
                            pos = elapsed % self._video_duration
                            self._current_time = pos
                            self._scrubber.set((pos / self._video_duration) * 100)
                            self._update_time_label(pos)
        except Exception:
            pass
        self.root.after(15, self._credits_display_loop)

    def _credits_resize(self, event=None):
        pass

    def close_credits(self):
        self._credits_stop.set()
        proc = self._credits_process
        self._credits_process = None
        if proc:
            try:
                proc.kill()
            except:
                pass
            try:
                proc.stdout.close()
            except:
                pass
        if self._credits_audio:
            wav_path, sound = self._credits_audio
            try:
                sound.stop()
            except:
                pass
            try:
                os.remove(wav_path)
            except:
                pass
            self._credits_audio = None
        win = self._credits_window
        self._credits_window = None
        self._credits_photo = None
        if win:
            try:
                win.destroy()
            except:
                pass

    def open_howto(self):
        self.open_credits("howto.mp4", "How To", show_scrubber=True)

    # ---------- AUDIO TIMELINE ----------
    def get_audio_duration(self, path):
        try:
            with wave.open(path, 'rb') as wf:
                frames = wf.getnframes()
                rate = wf.getframerate()
                if rate > 0:
                    return frames / float(rate)
        except:
            pass
        if shutil.which("ffprobe"):
            try:
                result = subprocess.run(
                    ["ffprobe", "-v", "error", "-show_entries", "format=duration",
                     "-of", "csv=p=0", path],
                    capture_output=True, text=True, timeout=5
                )
                dur = float(result.stdout.strip())
                if dur > 0:
                    return dur
            except:
                pass
        return 3.0

    def get_audio_duration_cached(self, path):
        if path not in self.duration_cache:
            self.duration_cache[path] = self.get_audio_duration(path)
        return self.duration_cache[path]

    def compute_waveform(self, path, num_bars=80):
        try:
            with wave.open(path, 'rb') as wf:
                n_channels = wf.getnchannels()
                samp_width = wf.getsampwidth()
                n_frames = wf.getnframes()
                raw = wf.readframes(n_frames)
            if samp_width == 1:
                samples = struct.unpack(f"<{n_frames * n_channels}B", raw)
                samples = [s - 128 for s in samples]
                max_val = 128
            elif samp_width == 2:
                samples = struct.unpack(f"<{n_frames * n_channels}h", raw)
                max_val = 32768
            elif samp_width == 4:
                samples = struct.unpack(f"<{n_frames * n_channels}i", raw)
                max_val = 2**31
            else:
                raise ValueError("Unsupported sample width")
            if n_channels > 1:
                samples = samples[0::n_channels]
            total = len(samples)
            if total == 0:
                raise ValueError("Empty audio stream")
            chunk = max(1, total // num_bars)
            bars = []
            for i in range(num_bars):
                start = i * chunk
                end = min(total, start + chunk)
                if start >= total:
                    bars.append(0.05)
                    continue
                segment = samples[start:end]
                peak = max(abs(s) for s in segment) if segment else 0
                bars.append(min(1.0, peak / max_val))
            return bars
        except:
            seed = sum(ord(c) for c in os.path.basename(path))
            rnd = random.Random(seed)
            return [0.15 + 0.7 * rnd.random() for _ in range(num_bars)]

    def get_waveform_cached(self, path):
        if path not in self.waveform_cache:
            self.waveform_cache[path] = self.compute_waveform(path)
        return self.waveform_cache[path]

    def get_audio_library_dir(self):
        if getattr(sys, 'frozen', False):
            if sys.platform == 'win32':
                base = os.getenv('APPDATA', os.path.expanduser('~'))
            else:
                base = os.path.expanduser('~/.local/share')
            lib_dir = os.path.join(base, 'Freenimate', 'sounds', 'library')
            os.makedirs(lib_dir, exist_ok=True)
            return lib_dir
        else:
            return resource_path(os.path.join("sounds", "library"))

    def get_library_sounds(self):
        valid_ext = {".wav", ".mp3", ".ogg", ".flac", ".aiff", ".aif", ".m4a"}
        lib_dir = self.get_audio_library_dir()
        sounds = []
        seen = set()
        if os.path.isdir(lib_dir):
            for fname in sorted(os.listdir(lib_dir), key=str.lower):
                full_path = os.path.join(lib_dir, fname)
                if not os.path.isfile(full_path):
                    continue
                if os.path.splitext(fname)[1].lower() not in valid_ext:
                    continue
                real_path = os.path.normcase(os.path.abspath(full_path))
                if real_path in seen:
                    continue
                seen.add(real_path)
                sounds.append({"name": fname, "path": full_path})
        if not getattr(sys, 'frozen', False):
            dev_dir = resource_path("sounds")
            if os.path.isdir(dev_dir):
                for fname in sorted(os.listdir(dev_dir), key=str.lower):
                    full_path = os.path.join(dev_dir, fname)
                    if not os.path.isfile(full_path):
                        continue
                    if os.path.splitext(fname)[1].lower() not in valid_ext:
                        continue
                    real_path = os.path.normcase(os.path.abspath(full_path))
                    if real_path in seen:
                        continue
                    seen.add(real_path)
                    sounds.append({"name": fname, "path": full_path})
        sounds.sort(key=lambda item: item["name"].lower())
        return sounds

    def add_custom_sound(self):
        paths = filedialog.askopenfilenames(
            title="Add Custom Sound(s)",
            filetypes=[("Audio Files", "*.wav *.mp3 *.ogg *.flac *.aiff *.aif *.m4a"), ("All Files", "*.*")]
        )
        if not paths:
            return
        lib_dir = self.get_audio_library_dir()
        try:
            os.makedirs(lib_dir, exist_ok=True)
        except Exception as e:
            self.show_alert("Add Sound Error", f"Could not create the sound library folder:\n{e}")
            return
        added_any = False
        for src in paths:
            try:
                base, ext = os.path.splitext(os.path.basename(src))
                dest_path = os.path.join(lib_dir, base + ext)
                counter = 1
                while os.path.exists(dest_path):
                    dest_path = os.path.join(lib_dir, f"{base}_{counter}{ext}")
                    counter += 1
                shutil.copy2(src, dest_path)
                added_any = True
            except Exception as e:
                self.show_alert("Add Sound Error", f"Could not add {os.path.basename(src)}:\n{e}")
        if added_any:
            self.refresh_audio_library_list()

    def open_audio_window(self):
        if self.audio_win is not None and self.audio_win.winfo_exists():
            self.audio_win.lift()
            return
        self.audio_win = tk.Toplevel(self.root)
        self.audio_win.title("Audio Timeline")
        self.audio_win.geometry("1040x540")
        self.audio_win.configure(bg="#2a2a2a")
        self.audio_win.transient(self.root)
        self.audio_win.minsize(760, 400)
        self._audio_drag = None
        self._clip_drag = None
        self._clip_drag_ghost = None
        main_pane = tk.Frame(self.audio_win, bg="#2a2a2a")
        main_pane.pack(fill=tk.BOTH, expand=True)

        lib_frame = tk.Frame(main_pane, bg="#232323", width=260)
        lib_frame.pack(side=tk.LEFT, fill=tk.Y)
        lib_frame.pack_propagate(False)
        tk.Label(lib_frame, text="Sound Library", bg="#232323", fg="white",
                 font=("Arial", 10, "bold")).pack(pady=(10, 6), padx=10, anchor="w")
        add_icon = self.load_icon("add.png", (18, 18))
        add_btn = tk.Button(lib_frame, text="Add Custom Sound",
                            image=add_icon if add_icon else None,
                            compound=tk.LEFT if add_icon else "none",
                            bg="#444", fg="white", font=("Arial", 9, "bold"),
                            anchor="w", relief=tk.FLAT, padx=8, pady=6,
                            command=self.add_custom_sound)
        if add_icon:
            add_btn.image = add_icon
        add_btn.pack(fill=tk.X, padx=10, pady=(0, 8))

        lib_scroll_outer = tk.Frame(lib_frame, bg="#232323")
        lib_scroll_outer.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 6))
        self.audio_lib_canvas = tk.Canvas(lib_scroll_outer, bg="#232323", highlightthickness=0, bd=0)
        self.audio_lib_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        lib_scrollbar = tk.Scrollbar(lib_scroll_outer, orient=tk.VERTICAL,
                                     command=self.audio_lib_canvas.yview,
                                     width=14, bg="#505050", activebackground="#707070",
                                     troughcolor="#1a1a1a", relief=tk.FLAT, bd=0)
        lib_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.audio_lib_canvas.pack_forget()
        self.audio_lib_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.audio_lib_canvas.configure(yscrollcommand=lib_scrollbar.set)
        self.audio_lib_list_frame = tk.Frame(self.audio_lib_canvas, bg="#232323")
        self.audio_lib_window_id = self.audio_lib_canvas.create_window(
            (0, 0), window=self.audio_lib_list_frame, anchor="nw"
        )

        def update_library_scrollregion(_event=None):
            self.audio_lib_canvas.configure(scrollregion=self.audio_lib_canvas.bbox("all"))
        def resize_library_inner(_event):
            self.audio_lib_canvas.itemconfigure(
                self.audio_lib_window_id,
                width=max(1, self.audio_lib_canvas.winfo_width())
            )
        self.audio_lib_list_frame.bind("<Configure>", update_library_scrollregion)
        self.audio_lib_canvas.bind("<Configure>", resize_library_inner)
        def on_lib_wheel(event):
            self.audio_lib_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            return "break"
        self.audio_lib_canvas.bind("<MouseWheel>", on_lib_wheel)
        self.audio_lib_list_frame.bind("<MouseWheel>", on_lib_wheel)

        timeline_frame = tk.Frame(main_pane, bg="#2a2a2a")
        timeline_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tk.Label(timeline_frame, text="Drag sounds from the library onto the timeline.",
                 bg="#2a2a2a", fg="#aaaaaa", font=("Arial", 8),
                 wraplength=760, justify=tk.LEFT).pack(anchor="w", padx=10, pady=(10, 4))
        timeline_canvas_outer = tk.Frame(timeline_frame, bg="#2a2a2a")
        timeline_canvas_outer.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        h_scroll = tk.Scrollbar(timeline_canvas_outer, orient=tk.HORIZONTAL)
        h_scroll.pack(side=tk.BOTTOM, fill=tk.X)
        self.audio_timeline_canvas = tk.Canvas(timeline_canvas_outer, bg="#1e1e1e", highlightthickness=0,
                                               xscrollcommand=h_scroll.set)
        self.audio_timeline_canvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        h_scroll.config(command=self.audio_timeline_canvas.xview)
        self.audio_timeline_canvas.bind("<Configure>", lambda e: self.redraw_audio_timeline())

        def on_close():
            self.stop_audio_preview()
            self.stop_playback_audio()
            if self._audio_redraw_job is not None:
                try: self.audio_win.after_cancel(self._audio_redraw_job)
                except: pass
                self._audio_redraw_job = None
            self.audio_win.destroy()
            self.audio_win = None
        self.audio_win.protocol("WM_DELETE_WINDOW", on_close)
        self.refresh_audio_library_list()
        self.redraw_audio_timeline()

    def refresh_audio_library_list(self):
        for widget in self.audio_lib_list_frame.winfo_children():
            widget.destroy()
        self.audio_lib_list_frame.grid_columnconfigure(0, weight=1, uniform="sound_col")
        self.audio_lib_list_frame.grid_columnconfigure(1, weight=1, uniform="sound_col")
        sounds = self.get_library_sounds()
        speaker_icon = self.load_icon("speaker.png", (22, 22))
        play_icon = self.load_icon("play.png", (14, 14))
        if not sounds:
            empty = tk.Label(self.audio_lib_list_frame,
                             text="Sound Library\n\nNo sound files found.\nUse “Add Custom Sound” to add them.",
                             bg="#232323", fg="#888888", font=("Arial", 8),
                             justify=tk.CENTER)
            empty.grid(row=0, column=0, columnspan=2, padx=6, pady=18, sticky="nsew")
            self.audio_lib_list_frame.grid_rowconfigure(0, weight=1)
            self.audio_lib_canvas.configure(scrollregion=(0, 0, 1, 220))
            return
        for index, sound in enumerate(sounds):
            r = index // 2
            c = index % 2
            card = tk.Frame(self.audio_lib_list_frame, bg="#343434", bd=1, relief=tk.FLAT,
                            width=110, height=100, cursor="hand2")
            card.grid(row=r, column=c, padx=4, pady=4, sticky="nsew")
            card.grid_propagate(False)
            icon_lbl = tk.Label(card, image=speaker_icon if speaker_icon else None,
                                text="SFX" if not speaker_icon else "",
                                bg="#343434", fg="white", font=("Arial", 7, "bold"),
                                cursor="hand2")
            if speaker_icon:
                icon_lbl.image = speaker_icon
            icon_lbl.pack(pady=(5, 2))
            name_lbl = tk.Label(card, text=sound["name"], bg="#343434", fg="white",
                                font=("Arial", 8, "bold"), wraplength=96,
                                justify=tk.CENTER, cursor="hand2")
            name_lbl.pack(fill=tk.X, expand=True, padx=2)
            play_btn = tk.Button(card, image=play_icon if play_icon else None,
                                 text="▶" if not play_icon else "",
                                 bg="#4a4a4a", fg="white", activebackground="#5a5a5a",
                                 relief=tk.FLAT, bd=0, padx=5, pady=2,
                                 command=lambda p=sound["path"]: self.play_audio_file(p))
            if play_icon:
                play_btn.image = play_icon
            play_btn.pack(pady=(2, 4))
            for widget in (card, icon_lbl, name_lbl):
                widget.bind("<ButtonPress-1>", lambda e, s=sound: self.start_library_drag(e, s))
                widget.bind("<B1-Motion>", self.on_library_drag_motion)
                widget.bind("<ButtonRelease-1>", self.on_library_drag_release)

    def start_library_drag(self, event, sound):
        self._audio_drag = {
            "sound": sound,
            "duration": self.get_audio_duration_cached(sound["path"]),
            "press_x": event.x_root, "press_y": event.y_root,
            "ghost": None, "started": False,
        }

    def on_library_drag_motion(self, event):
        drag = self._audio_drag
        if not drag:
            return
        dx = event.x_root - drag["press_x"]
        dy = event.y_root - drag["press_y"]
        if not drag["started"]:
            if dx*dx + dy*dy < 100:
                return
            ghost = tk.Toplevel(self.audio_win)
            ghost.overrideredirect(True)
            try:
                ghost.attributes("-alpha", 0.85)
                ghost.attributes("-topmost", True)
            except:
                pass
            tk.Label(ghost, text=drag["sound"]["name"], bg="#3fae57", fg="#0d2e17",
                     font=("Arial", 9, "bold"), padx=8, pady=4).pack()
            drag["ghost"] = ghost
            drag["started"] = True
        ghost = drag["ghost"]
        if ghost is not None and ghost.winfo_exists():
            ghost.geometry(f"+{event.x_root + 12}+{event.y_root + 12}")

    def on_library_drag_release(self, event):
        drag = self._audio_drag
        self._audio_drag = None
        if not drag:
            return
        ghost = drag.get("ghost")
        if ghost is not None:
            try: ghost.destroy()
            except: pass
        if not drag.get("started"):
            return
        canvas = self.audio_timeline_canvas
        cx0, cy0 = canvas.winfo_rootx(), canvas.winfo_rooty()
        cw, ch = canvas.winfo_width(), canvas.winfo_height()
        if cx0 <= event.x_root <= cx0 + cw and cy0 <= event.y_root <= cy0 + ch:
            local_x = canvas.canvasx(event.x_root - cx0)
            local_y = canvas.canvasy(event.y_root - cy0)
            self.add_audio_clip(drag["sound"], drag["duration"], local_x, local_y)

    def add_audio_clip(self, sound, duration, drop_x, drop_y):
        track_idx = max(0, int((drop_y - self.AUDIO_RULER_H) // self.AUDIO_TRACK_H))
        start_time = max(0.0, drop_x / self.AUDIO_PX_PER_SEC)
        self.audio_clip_counter += 1
        clip = {
            "id": self.audio_clip_counter,
            "name": sound["name"],
            "path": sound["path"],
            "track": track_idx,
            "start": start_time,
            "duration": duration,
            "trim_start": 0.0,
            "trim_end": 0.0,
            "volume": 1.0,
        }
        self.audio_clips.append(clip)
        self.redraw_audio_timeline()

    def schedule_audio_timeline_redraw(self):
        canvas = getattr(self, "audio_timeline_canvas", None)
        if not canvas or not canvas.winfo_exists() or self._audio_redraw_job is not None:
            return
        self._audio_redraw_job = self.audio_win.after(33, self._run_scheduled_audio_redraw)

    def _run_scheduled_audio_redraw(self):
        self._audio_redraw_job = None
        self.redraw_audio_timeline()

    def redraw_audio_timeline(self):
        canvas = getattr(self, "audio_timeline_canvas", None)
        if not canvas or not canvas.winfo_exists():
            return
        canvas.delete("all")
        max_track = max((c["track"] for c in self.audio_clips), default=-1)
        num_tracks = max(self.AUDIO_NUM_TRACKS, max_track + 1)
        max_end_time = 0.0
        for c in self.audio_clips:
            visible_dur = max(0.05, c["duration"] - c["trim_start"] - c["trim_end"])
            max_end_time = max(max_end_time, c["start"] + visible_dur)
        total_seconds = max(20.0, max_end_time + 5.0)
        total_width = int(total_seconds * self.AUDIO_PX_PER_SEC) + 40
        total_height = self.AUDIO_RULER_H + num_tracks * self.AUDIO_TRACK_H + 10
        canvas.configure(scrollregion=(0, 0, total_width, total_height))
        canvas.create_rectangle(0, 0, total_width, self.AUDIO_RULER_H, fill="#141414", outline="")
        sec = 0
        while sec <= total_seconds:
            x = sec * self.AUDIO_PX_PER_SEC
            canvas.create_line(x, 0, x, total_height, fill="#333333")
            canvas.create_text(x + 3, self.AUDIO_RULER_H / 2, text=f"{sec}s", fill="#999999",
                               font=("Arial", 7), anchor="w")
            sec += 1
        for t in range(num_tracks):
            y0 = self.AUDIO_RULER_H + t * self.AUDIO_TRACK_H
            y1 = y0 + self.AUDIO_TRACK_H
            lane_color = "#1c1c1c" if t % 2 == 0 else "#202020"
            canvas.create_rectangle(0, y0, total_width, y1, fill=lane_color, outline="")
        for clip in self.audio_clips:
            self.draw_audio_clip(canvas, clip)

    def draw_audio_clip(self, canvas, clip):
        px_per_sec = self.AUDIO_PX_PER_SEC
        visible_dur = max(0.05, clip["duration"] - clip["trim_start"] - clip["trim_end"])
        x0 = clip["start"] * px_per_sec
        x1 = x0 + visible_dur * px_per_sec
        y0 = self.AUDIO_RULER_H + clip["track"] * self.AUDIO_TRACK_H + self.AUDIO_TRACK_PAD
        y1 = y0 + self.AUDIO_TRACK_H - 2 * self.AUDIO_TRACK_PAD
        tag = f"clip_{clip['id']}"
        tags = ("clip", tag)
        canvas.create_rectangle(x0, y0, x1, y1, fill="#3fae57", outline="#1f6b34", width=1.5, tags=tags)
        bars = self.get_waveform_cached(clip["path"])
        n = len(bars)
        vol_y0 = y1 - self.AUDIO_VOL_ZONE
        if n > 0 and x1 - x0 > 4:
            total_dur = max(0.001, clip["duration"])
            start_frac = clip["trim_start"] / total_dur
            end_frac = 1.0 - (clip["trim_end"] / total_dur)
            start_idx = int(start_frac * n)
            end_idx = max(start_idx + 1, int(end_frac * n))
            visible_bars = bars[start_idx:end_idx] or [0.15]
            mid_y = (y0 + vol_y0) / 2
            avail_h = (vol_y0 - y0) - 6
            bar_w = max(1.0, (x1 - x0) / len(visible_bars))
            for i, amp in enumerate(visible_bars):
                bx = x0 + i * bar_w
                bar_h = max(2, amp * avail_h / 2)
                canvas.create_line(bx, mid_y - bar_h, bx, mid_y + bar_h,
                                   fill="#1f5c30", width=max(1, int(bar_w * 0.8)), tags=tags)
        canvas.create_rectangle(x0, vol_y0, x1, y1, fill="#245c33", outline="", tags=tags)
        vol_fill_w = (x1 - x0) * clip["volume"]
        canvas.create_rectangle(x0, vol_y0, x0 + vol_fill_w, y1, fill="#7CFC8C", outline="", tags=tags)
        canvas.create_text(x1 - 4, (vol_y0 + y1) / 2, text=f"{int(clip['volume'] * 100)}%",
                           fill="#0d2e17", font=("Arial", 7, "bold"), anchor="e", tags=tags)
        canvas.tag_bind(tag, "<ButtonPress-1>", lambda e, c=clip: self.on_clip_press(e, c))
        canvas.tag_bind(tag, "<B1-Motion>", self.on_clip_drag)
        canvas.tag_bind(tag, "<ButtonRelease-1>", self.on_clip_release)
        canvas.tag_bind(tag, "<Motion>", lambda e, c=clip: self.on_clip_hover(e, c))
        canvas.tag_bind(tag, "<Double-Button-1>", lambda e, c=clip: self.on_clip_double_click(e, c))

    def on_clip_press(self, event, clip):
        canvas = self.audio_timeline_canvas
        cx = canvas.canvasx(event.x)
        cy = canvas.canvasy(event.y)
        px_per_sec = self.AUDIO_PX_PER_SEC
        visible_dur = max(0.05, clip["duration"] - clip["trim_start"] - clip["trim_end"])
        x0 = clip["start"] * px_per_sec
        x1 = x0 + visible_dur * px_per_sec
        y0 = self.AUDIO_RULER_H + clip["track"] * self.AUDIO_TRACK_H + self.AUDIO_TRACK_PAD
        y1 = y0 + self.AUDIO_TRACK_H - 2 * self.AUDIO_TRACK_PAD
        vol_y0 = y1 - self.AUDIO_VOL_ZONE
        if cx <= x0 + self.AUDIO_EDGE:
            mode = "trim_start"
        elif cx >= x1 - self.AUDIO_EDGE:
            mode = "trim_end"
        elif cy >= vol_y0:
            mode = "volume"
        else:
            mode = "move"
        self._clip_drag = {
            "clip": clip,
            "mode": mode,
            "start_x": cx,
            "start_y": cy,
            "orig_start": clip["start"],
            "orig_trim_start": clip["trim_start"],
            "orig_trim_end": clip["trim_end"],
            "orig_volume": clip["volume"],
            "orig_track": clip["track"],
        }
        if mode == "move":
            self._create_clip_ghost(clip, x0, x1, y0, y1)

    def _create_clip_ghost(self, clip, x0, x1, y0, y1):
        canvas = self.audio_timeline_canvas
        self._clip_drag_ghost = canvas.create_rectangle(
            x0, y0, x1, y1,
            fill="#3fae57", outline="#1f6b34", width=1.5,
            stipple="gray50", tags="ghost"
        )

    def on_clip_drag(self, event):
        drag = self._clip_drag
        if not drag:
            return
        clip = drag["clip"]
        canvas = self.audio_timeline_canvas
        cx = canvas.canvasx(event.x)
        cy = canvas.canvasy(event.y)
        dx = cx - drag["start_x"]
        dy = cy - drag["start_y"]
        px_per_sec = self.AUDIO_PX_PER_SEC
        if drag["mode"] == "move":
            clip["start"] = max(0.0, drag["orig_start"] + dx / px_per_sec)
            track_delta = round(dy / self.AUDIO_TRACK_H)
            clip["track"] = max(0, drag["orig_track"] + track_delta)
            if self._clip_drag_ghost:
                visible_dur = max(0.05, clip["duration"] - clip["trim_start"] - clip["trim_end"])
                x0 = clip["start"] * px_per_sec
                x1 = x0 + visible_dur * px_per_sec
                y0 = self.AUDIO_RULER_H + clip["track"] * self.AUDIO_TRACK_H + self.AUDIO_TRACK_PAD
                y1 = y0 + self.AUDIO_TRACK_H - 2 * self.AUDIO_TRACK_PAD
                canvas.coords(self._clip_drag_ghost, x0, y0, x1, y1)
        elif drag["mode"] == "trim_start":
            delta_time = dx / px_per_sec
            max_trim = max(0.0, clip["duration"] - clip["trim_end"] - 0.05)
            new_trim_start = min(max(0.0, drag["orig_trim_start"] + delta_time), max_trim)
            shift = new_trim_start - drag["orig_trim_start"]
            clip["trim_start"] = new_trim_start
            clip["start"] = max(0.0, drag["orig_start"] + shift)
        elif drag["mode"] == "trim_end":
            delta_time = -dx / px_per_sec
            max_trim = max(0.0, clip["duration"] - clip["trim_start"] - 0.05)
            clip["trim_end"] = min(max(0.0, drag["orig_trim_end"] + delta_time), max_trim)
        elif drag["mode"] == "volume":
            delta_vol = -dy / 100.0
            clip["volume"] = min(1.0, max(0.0, drag["orig_volume"] + delta_vol))
        self.schedule_audio_timeline_redraw()

    def on_clip_release(self, event):
        if self._clip_drag_ghost:
            try:
                canvas = self.audio_timeline_canvas
                canvas.delete(self._clip_drag_ghost)
            except:
                pass
            self._clip_drag_ghost = None
        self._clip_drag = None
        if self._audio_redraw_job is not None:
            try: self.audio_win.after_cancel(self._audio_redraw_job)
            except: pass
            self._audio_redraw_job = None
        self.redraw_audio_timeline()

    def on_clip_hover(self, event, clip):
        canvas = self.audio_timeline_canvas
        cx = canvas.canvasx(event.x)
        cy = canvas.canvasy(event.y)
        px_per_sec = self.AUDIO_PX_PER_SEC
        visible_dur = max(0.05, clip["duration"] - clip["trim_start"] - clip["trim_end"])
        x0 = clip["start"] * px_per_sec
        x1 = x0 + visible_dur * px_per_sec
        if cx <= x0 + self.AUDIO_EDGE or cx >= x1 - self.AUDIO_EDGE:
            canvas.configure(cursor="sb_h_double_arrow")
        else:
            y0 = self.AUDIO_RULER_H + clip["track"] * self.AUDIO_TRACK_H + self.AUDIO_TRACK_PAD
            y1 = y0 + self.AUDIO_TRACK_H - 2 * self.AUDIO_TRACK_PAD
            vol_y0 = y1 - self.AUDIO_VOL_ZONE
            canvas.configure(cursor="sb_v_double_arrow" if cy >= vol_y0 else "fleur")

    def on_clip_double_click(self, event, clip):
        if clip in self.audio_clips:
            self.audio_clips.remove(clip)
            self.redraw_audio_timeline()

    # ---------- AUDIO PLAYBACK ----------
    def _play_audio_pygame(self, path, volume=1.0, duration=None):
        try:
            if path not in self._pygame_sounds:
                self._pygame_sounds[path] = pygame.mixer.Sound(path)
            sound = self._pygame_sounds[path]
            if volume != 1.0:
                sound.set_volume(min(1.0, max(0.0, volume)))
            sound.play()
            if duration is not None:
                time.sleep(duration)
                sound.stop()
            return True
        except Exception as e:
            print(f"Pygame playback error: {e}")
            return False

    def play_audio_for_animation(self):
        self.stop_playback_audio()
        if not self.audio_clips:
            return
        total_frames = len(self.frames)
        animation_duration = total_frames / self.fps
        self.playback_start_time = time.time()
        for clip in self.audio_clips:
            clip_start = clip["start"]
            clip_duration = clip["duration"] - clip["trim_start"] - clip["trim_end"]
            if clip_start >= animation_duration:
                continue
            play_duration = min(clip_duration, animation_duration - clip_start)
            if play_duration <= 0:
                continue
            self._start_audio_clip_instant(clip, clip_start, play_duration)

    def _start_audio_clip_instant(self, clip, start_time, duration):
        def play_clip_at_time():
            elapsed = time.time() - self.playback_start_time
            wait_time = start_time - elapsed
            if wait_time > 0.001:
                while wait_time > 0 and self.is_playing:
                    sleep_time = min(wait_time, 0.005)
                    time.sleep(sleep_time)
                    wait_time -= sleep_time
                    if not self.is_playing:
                        return
            if self.is_playing:
                if HAS_PYGAME:
                    self._play_audio_pygame(clip["path"], clip["volume"], duration)
                else:
                    self._play_audio_clip_fast(clip, duration)
        thread = threading.Thread(target=play_clip_at_time, daemon=True)
        thread.start()
        self._audio_playback_threads.append(thread)

    def _play_audio_clip_fast(self, clip, duration):
        try:
            ffplay = shutil.which("ffplay")
            if ffplay:
                cmd = [ffplay, "-nodisp", "-autoexit", "-loglevel", "quiet", "-vn",
                       "-analyzeduration", "0", "-probesize", "32", "-flags", "low_delay",
                       "-fflags", "nobuffer", "-avioflags", "direct"]
                if clip["volume"] != 1.0:
                    cmd.extend(["-af", f"volume={clip['volume']}"])
                if clip["trim_start"] > 0:
                    cmd.extend(["-ss", str(clip["trim_start"])])
                if duration > 0:
                    cmd.extend(["-t", str(duration)])
                cmd.append(clip["path"])
                proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                with self._audio_sync_lock:
                    self._playback_audio_processes.append(proc)
                proc.wait()
        except Exception as e:
            print(f"Audio playback error: {e}")

    def stop_playback_audio(self):
        if HAS_PYGAME:
            try: pygame.mixer.stop()
            except: pass
        with self._audio_sync_lock:
            for proc in self._playback_audio_processes:
                try:
                    if proc.poll() is None:
                        proc.terminate()
                except: pass
            self._playback_audio_processes.clear()
        for thread in self._audio_playback_threads:
            try:
                if thread.is_alive():
                    thread.join(0.01)
            except: pass
        self._audio_playback_threads.clear()

    def check_ffmpeg_installed(self):
        if shutil.which("ffmpeg") is not None:
            return True
        self.show_ffmpeg_missing_dialog()
        return False

    def show_ffmpeg_missing_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("FFmpeg Missing")
        win.geometry("460x180")
        win.configure(bg="#2a2a2a")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)
        win.update_idletasks()
        pw = self.root.winfo_width()
        ph = self.root.winfo_height()
        px = self.root.winfo_x()
        py = self.root.winfo_y()
        win.geometry(f"+{px + (pw // 2) - 230}+{py + (ph // 2) - 90}")
        content_f = tk.Frame(win, bg="#2a2a2a", padx=20, pady=20)
        content_f.pack(expand=True, fill=tk.BOTH)
        alert_icon = self.load_icon("smileywarn.png", (48, 48))
        if alert_icon:
            img_lbl = tk.Label(content_f, image=alert_icon, bg="#2a2a2a")
            img_lbl.image = alert_icon
            img_lbl.pack(side=tk.LEFT, padx=(0, 15), anchor="center")
        else:
            img_lbl = tk.Label(content_f, text="[!]", font=("Arial", 16, "bold"), bg="#2a2a2a", fg="#ffcc00")
            img_lbl.pack(side=tk.LEFT, padx=(0, 15), anchor="center")
        msg_lbl = tk.Label(content_f,
            text="It looks like you do not have an installation of FFmpeg! Download FFmpeg?",
            bg="#2a2a2a", fg="white", font=("Arial", 10, "bold"),
            wraplength=320, justify=tk.LEFT)
        msg_lbl.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        btn_f = tk.Frame(win, bg="#1e1e1e", pady=10, padx=15)
        btn_f.pack(fill=tk.X, side=tk.BOTTOM)
        def on_yes():
            win.destroy()
            webbrowser.open("https://ffmpeg.org/download.html")
        def on_no():
            win.destroy()
        tk.Button(btn_f, text="Yes", bg="#007acc", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=on_yes).pack(side=tk.RIGHT, padx=(6,0))
        tk.Button(btn_f, text="No", bg="#444444", fg="white", font=("Arial", 9, "bold"),
                  width=10, relief=tk.FLAT, command=on_no).pack(side=tk.RIGHT)

    # ---------- MENU AND UI ----------
    def create_menu(self):
        menubar = tk.Menu(self.root)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="New Project...", command=self.new_project_dialog)
        file_menu.add_separator()
        file_menu.add_command(label="Import MP4 Video...", command=self.import_mp4)
        file_menu.add_separator()
        file_menu.add_command(label="Save Project...", command=self.save_project)
        file_menu.add_command(label="Load Project...", command=self.load_project)
        file_menu.add_separator()
        file_menu.add_command(label="Settings...", command=self.open_settings)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        edit_menu = tk.Menu(menubar, tearoff=0)
        edit_menu.add_command(label="Undo", command=self.undo)
        edit_menu.add_command(label="Redo", command=self.redo)
        edit_menu.add_separator()
        edit_menu.add_command(label="Clear Active Layer", command=self.clear_active_layer)
        edit_menu.add_command(label="Settings...", command=self.open_settings)
        edit_menu.add_separator()
        edit_menu.add_command(label="Shortcut Editor...", command=self.open_shortcut_editor)
        menubar.add_cascade(label="Edit", menu=edit_menu)

        view_menu = tk.Menu(menubar, tearoff=0)
        view_menu.add_checkbutton(label="Toggle Onion Skinning", onvalue=True, offvalue=False,
                                  variable=tk.BooleanVar(value=self.onion_skin), command=self.toggle_onion_skin)
        view_menu.add_command(label="Reset Zoom / Pan", command=self.reset_view)
        menubar.add_cascade(label="View", menu=view_menu)

        render_menu = tk.Menu(menubar, tearoff=0)
        render_menu.add_command(label="Export Video...", command=self.export_video_with_audio)
        render_menu.add_command(label="Upload to Catbox...", command=self.upload_to_catbox)
        render_menu.add_command(label="Render GIF", command=self.export_gif)
        render_menu.add_command(label="Render PNG Sequence...", command=self.export_png_sequence)
        menubar.add_cascade(label="Render", menu=render_menu)

        self.root.config(menu=menubar)

    def open_settings(self):
        win = tk.Toplevel(self.root)
        win.title("Settings")
        win.geometry("420x320")
        win.configure(bg="#3a3a3a")
        win.transient(self.root)
        win.grab_set()

        tk.Label(win, text="Settings", font=("Arial", 12, "bold"), bg="#3a3a3a", fg="white").pack(pady=10)

        render_frame = tk.Frame(win, bg="#3a3a3a")
        render_frame.pack(fill=tk.X, padx=20, pady=8)
        tk.Label(render_frame, text="Render Mode:", font=("Arial", 10, "bold"), bg="#3a3a3a", fg="white").pack(side=tk.LEFT)
        render_var = tk.StringVar(value=self.render_mode)
        render_dropdown = ttk.Combobox(render_frame, textvariable=render_var,
                                      values=["CPU", "GPU"], width=10, state="readonly")
        render_dropdown.pack(side=tk.RIGHT, padx=10)
        render_dropdown.bind("<<ComboboxSelected>>", lambda e: setattr(self, 'render_mode', render_var.get()))

        scale_f = tk.Frame(win, bg="#3a3a3a")
        scale_f.pack(fill=tk.X, padx=20, pady=8)
        tk.Label(scale_f, text="UI Scale:", font=("Arial", 10, "bold"), bg="#3a3a3a", fg="white").pack(side=tk.LEFT)
        scale_lbl = tk.Label(scale_f, text=f"{int(self.ui_scale * 100)}%", bg="#3a3a3a", fg="white", width=6)
        scale_lbl.pack(side=tk.RIGHT)
        def on_scale_change(val):
            v = float(val)
            self.ui_scale = v
            scale_lbl.config(text=f"{int(v * 100)}%")
            self.root.tk.call('tk', 'scaling', v * 1.33)
            self.update_all_ui_icons()
        s_slider = tk.Scale(scale_f, from_=0.5, to=2.0, resolution=0.1, orient=tk.HORIZONTAL,
                            bg="#3a3a3a", fg="white", highlightthickness=0, troughcolor="#222",
                            showvalue=False, command=on_scale_change)
        s_slider.set(self.ui_scale)
        s_slider.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=10)

        fps_f = tk.Frame(win, bg="#3a3a3a")
        fps_f.pack(fill=tk.X, padx=20, pady=8)
        tk.Label(fps_f, text="Playback FPS:", font=("Arial", 10, "bold"), bg="#3a3a3a", fg="white").pack(side=tk.LEFT)
        fps_lbl = tk.Label(fps_f, text=f"{self.fps} FPS", bg="#3a3a3a", fg="white", width=6)
        fps_lbl.pack(side=tk.RIGHT)
        def on_fps_change(val):
            self.fps = int(val)
            fps_lbl.config(text=f"{self.fps} FPS")
        fps_slider = tk.Scale(fps_f, from_=1, to=30, resolution=1, orient=tk.HORIZONTAL,
                              bg="#3a3a3a", fg="white", highlightthickness=0, troughcolor="#222",
                              showvalue=False, command=on_fps_change)
        fps_slider.set(self.fps)
        fps_slider.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=10)

        blur_frame = tk.Frame(win, bg="#3a3a3a")
        blur_frame.pack(fill=tk.X, padx=20, pady=8)
        tk.Label(blur_frame, text="Blur Radius:", font=("Arial", 10, "bold"), bg="#3a3a3a", fg="white").pack(side=tk.LEFT)
        blur_lbl = tk.Label(blur_frame, text=f"{self.blur_radius}px", bg="#3a3a3a", fg="white", width=6)
        blur_lbl.pack(side=tk.RIGHT)
        def on_blur_change(val):
            self.blur_radius = int(val)
            blur_lbl.config(text=f"{self.blur_radius}px")
        blur_slider = tk.Scale(blur_frame, from_=1, to=30, resolution=1, orient=tk.HORIZONTAL,
                               bg="#3a3a3a", fg="white", highlightthickness=0, troughcolor="#222",
                               showvalue=False, command=on_blur_change)
        blur_slider.set(self.blur_radius)
        blur_slider.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=10)

        credits_frame = tk.Frame(win, bg="#3a3a3a")
        credits_frame.pack(fill=tk.X, padx=20, pady=10)
        tk.Button(credits_frame, text="🎬 View Credits", bg="#444", fg="#ffcc00",
                  font=("Arial", 10, "bold"), relief=tk.RAISED, padx=20, pady=8,
                  command=self.open_credits).pack(side=tk.LEFT, padx=5)
        tk.Button(credits_frame, text="❓ How To", bg="#444", fg="#ffffff",
                  font=("Arial", 10, "bold"), relief=tk.RAISED, padx=20, pady=8,
                  command=self.open_howto).pack(side=tk.LEFT, padx=5)

        def on_done():
            self.save_settings()
            win.destroy()
        tk.Button(win, text="Save & Done", bg="#007acc", fg="white", font=("Arial", 9, "bold"), width=12,
                  command=on_done).pack(pady=15)

    def update_all_ui_icons(self):
        playback_info = [("start.png", (28, 28)), ("play.png", (28, 28)), ("end.png", (28, 28))]
        for btn, (icon_file, base_size) in zip(self.playback_buttons, playback_info):
            img = self.load_icon(icon_file, base_size)
            if img: btn.config(image=img)
        tools_info = [
            ("pencil.png", "pencil"), ("eraser.png", "eraser"),
            ("marquee.png", "marquee"), ("smudge.png", "smudge"),
            ("blur.png", "blur"), ("text.png", "text"),
            ("shape.png", "shape"), ("zoom.png", "zoom"),
            ("eyedropper.png", "eyedropper"), ("selection.png", "selection"),
            ("redo.png", "redo"), ("undo.png", "undo"), ("audio.png", "audio")
        ]
        for icon_file, tool_id in tools_info:
            if tool_id in self.tool_buttons:
                img = self.load_icon(icon_file, (32, 32))
                if img: self.tool_buttons[tool_id].config(image=img)
        self.refresh_layers_ui()

    def create_ui(self):
        top_frame = tk.Frame(self.root, bg="#3a3a3a", pady=8)
        top_frame.pack(side=tk.TOP, fill=tk.X)
        p_container = tk.Frame(top_frame, bg="#3a3a3a")
        p_container.pack(anchor=tk.CENTER)
        play_btns_data = [
            ("start.png", "|<<", self.first_frame),
            ("play.png", "PLAY", self.toggle_play),
            ("end.png", ">>|", self.last_frame)
        ]
        self.playback_buttons = []
        for icon_file, fallback_text, cmd in play_btns_data:
            img = self.load_icon(icon_file, base_size=(28, 28))
            if img:
                btn = tk.Button(p_container, image=img, bg="#555", activebackground="#777",
                                relief=tk.FLAT, bd=0, padx=6, pady=4, command=cmd)
            else:
                btn = tk.Button(p_container, text=fallback_text, font=("Arial", 11, "bold"),
                                bg="#555", fg="white", relief=tk.FLAT, width=5, height=1, command=cmd)
            btn.pack(side=tk.LEFT, padx=6)
            self.playback_buttons.append(btn)
        self.play_button = self.playback_buttons[1]

        left_frame = tk.Frame(self.root, bg="#3a3a3a", padx=10, pady=5)
        left_frame.pack(side=tk.LEFT, fill=tk.Y)
        tool_grid = tk.Frame(left_frame, bg="#3a3a3a")
        tool_grid.pack(anchor=tk.N, pady=(0, 10))
        tools_info = [
            ("pencil.png", "pencil"), ("eraser.png", "eraser"),
            ("marquee.png", "marquee"), ("smudge.png", "smudge"),
            ("blur.png", "blur"), ("text.png", "text"),
            ("shape.png", "shape"), ("zoom.png", "zoom"),
            ("eyedropper.png", "eyedropper"), ("selection.png", "selection"),
            ("redo.png", "redo"), ("undo.png", "undo"), ("audio.png", "audio")
        ]
        for i, (tool_file, tool_id) in enumerate(tools_info):
            row, col = divmod(i, 4)
            img = self.load_icon(tool_file, base_size=(32, 32))
            bg_color = "#555555" if tool_id == self.current_tool else "#2a2a2a"
            command = self.open_audio_window if tool_id == "audio" else (lambda t=tool_id: self.select_tool(t))
            if img:
                btn = tk.Button(tool_grid, image=img, bg=bg_color, activebackground="#555",
                                relief=tk.RIDGE, bd=1, command=command)
            else:
                btn = tk.Button(tool_grid, text=tool_id[:3].upper(), fg="white", bg=bg_color,
                                activebackground="#555", relief=tk.RIDGE, width=3, height=1,
                                command=command)
            btn.grid(row=row, column=col, padx=2, pady=2)
            self.tool_buttons[tool_id] = btn

        layers_outer = tk.LabelFrame(left_frame, text="Layers", bg="#3a3a3a", fg="white", padx=5, pady=5)
        layers_outer.pack(fill=tk.X, pady=(0, 10))
        layer_ctrl_bar = tk.Frame(layers_outer, bg="#3a3a3a")
        layer_ctrl_bar.pack(fill=tk.X, pady=(0, 4))
        tk.Button(layer_ctrl_bar, text="+ Layer", bg="#444", fg="white", font=("Arial", 8, "bold"),
                  command=self.add_layer).pack(side=tk.RIGHT, padx=2)
        tk.Button(layer_ctrl_bar, text="- Delete", bg="#444", fg="white", font=("Arial", 8, "bold"),
                  command=self.delete_active_layer).pack(side=tk.RIGHT, padx=2)
        self.layers_container = tk.Frame(layers_outer, bg="#3a3a3a")
        self.layers_container.pack(fill=tk.X)

        brush_ctrl_frame = tk.LabelFrame(left_frame, text="Brush Settings", bg="#3a3a3a", fg="white", padx=5, pady=5)
        brush_ctrl_frame.pack(fill=tk.X, pady=5)
        brush_select_frame = tk.Frame(brush_ctrl_frame, bg="#3a3a3a")
        brush_select_frame.pack(fill=tk.X, pady=2)
        tk.Label(brush_select_frame, text="Brush:", bg="#3a3a3a", fg="white",
                font=("Arial", 9, "bold")).pack(side=tk.LEFT, padx=(0, 5))
        self.brush_var = tk.StringVar(value=self.current_brush_name)
        brush_dropdown = ttk.Combobox(brush_select_frame, textvariable=self.brush_var,
                                      values=self.brush_names, width=15, state="readonly")
        brush_dropdown.pack(side=tk.LEFT, padx=5)
        brush_dropdown.bind("<<ComboboxSelected>>", self.on_brush_select)
        slider_frame = tk.Frame(brush_ctrl_frame, bg="#3a3a3a")
        slider_frame.pack(fill=tk.X, pady=(6, 2))
        self.size_label = tk.Label(slider_frame, text=f"{self.brush_size}pt", bg="#3a3a3a", fg="white",
                                   font=("Arial", 9, "bold"), width=6)
        self.size_label.pack(side=tk.RIGHT)
        self.size_slider = tk.Scale(slider_frame, from_=1, to=200, orient=tk.HORIZONTAL,
                                    bg="#3a3a3a", fg="white", highlightthickness=0, troughcolor="#222",
                                    showvalue=False, command=self.on_size_change)
        self.size_slider.set(self.brush_size)
        self.size_slider.pack(side=tk.LEFT, expand=True, fill=tk.X)

        right_frame = tk.Frame(self.root, bg="#3a3a3a", padx=10, pady=10)
        right_frame.pack(side=tk.RIGHT, fill=tk.Y)
        self.wheel_size = 140
        self.wheel_canvas = tk.Canvas(right_frame, width=self.wheel_size, height=self.wheel_size + 15,
                                      bg="#3a3a3a", highlightthickness=0)
        self.wheel_canvas.pack(pady=(0, 5))
        self.draw_color_wheel()
        self.wheel_canvas.bind("<Button-1>", self.on_wheel_click)
        self.wheel_canvas.bind("<B1-Motion>", self.on_wheel_click)
        self.wheel_canvas.bind("<Double-Button-1>", self.on_wheel_double_click)

        self.color_preview = tk.Frame(right_frame, bg=self.current_color, width=120, height=50,
                                      highlightbackground="white", highlightthickness=1)
        self.color_preview.pack(pady=5)
        tk.Button(right_frame, text="Save color..", bg="#2a2a2a", fg="white", relief=tk.RAISED,
                  font=("Arial", 9), anchor="w", padx=6, pady=2, command=self.save_current_color).pack(fill=tk.X, pady=6)
        swatch_frame = tk.Frame(right_frame, bg="#3a3a3a")
        swatch_frame.pack()
        for i, color in enumerate(self.swatch_colors):
            row, col = divmod(i, 3)
            btn = tk.Button(swatch_frame, bg=color, width=4, height=2, relief=tk.FLAT, bd=1,
                            command=lambda c_idx=i: self.select_swatch_color(c_idx))
            btn.grid(row=row, column=col, padx=2, pady=2)
            self.swatch_buttons.append(btn)

        bottom_frame = tk.Frame(self.root, bg="#2a2a2a", pady=6, padx=10)
        bottom_frame.pack(side=tk.BOTTOM, fill=tk.X)
        tb_top = tk.Frame(bottom_frame, bg="#2a2a2a")
        tb_top.pack(fill=tk.X, pady=(0, 4))
        tk.Label(tb_top, text="Timeline", font=("Arial", 10, "bold"), bg="#2a2a2a", fg="white").pack(side=tk.LEFT)
        self.onion_btn = tk.Button(tb_top, text="Onion Skin: ON" if self.onion_skin else "Onion Skin: OFF",
                                   bg="#007acc" if self.onion_skin else "#555", fg="white", font=("Arial", 8, "bold"),
                                   command=self.toggle_onion_skin)
        self.onion_btn.pack(side=tk.LEFT, padx=15)
        tk.Button(tb_top, text="+ Add Frame", bg="#444", fg="white", font=("Arial", 8, "bold"),
                  command=self.add_frame).pack(side=tk.RIGHT, padx=2)
        tk.Button(tb_top, text="Duplicate Frame", bg="#444", fg="white", font=("Arial", 8, "bold"),
                  command=self.duplicate_frame).pack(side=tk.RIGHT, padx=2)
        tk.Button(tb_top, text="- Delete Frame", bg="#444", fg="white", font=("Arial", 8, "bold"),
                  command=self.delete_frame).pack(side=tk.RIGHT, padx=2)

        timeline_scroll_container = tk.Frame(bottom_frame, bg="#1e1e1e")
        timeline_scroll_container.pack(fill=tk.X, expand=True)
        self.timeline_scrollbar = tk.Scrollbar(timeline_scroll_container, orient=tk.HORIZONTAL,
                                               bg="#333333", activebackground="#555555",
                                               troughcolor="#1a1a1a", width=14)
        self.timeline_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.timeline_scroll = tk.Canvas(timeline_scroll_container, bg="#1e1e1e", height=70,
                                         highlightthickness=0, xscrollcommand=self.timeline_scrollbar.set)
        self.timeline_scroll.pack(fill=tk.X, expand=True)
        self.timeline_scrollbar.config(command=self.timeline_scroll.xview)
        self.timeline_inner = tk.Frame(self.timeline_scroll, bg="#1e1e1e")
        self.timeline_window = self.timeline_scroll.create_window((0, 0), window=self.timeline_inner, anchor="nw")
        self.timeline_scroll.bind("<Configure>", lambda e: self.update_visible_timeline_frames())
        def on_timeline_wheel(event):
            self._scroll_position = self.timeline_scroll.xview()[0]
            self.timeline_scroll.xview_scroll(int(-1 * (event.delta / 120)), "units")
            self._scroll_position = self.timeline_scroll.xview()[0]
            self.update_visible_timeline_frames()
        self.timeline_scroll.bind_all("<MouseWheel>", on_timeline_wheel)
        self.timeline_scroll.bind("<ButtonPress-1>", self._start_canvas_timeline_drag)
        self.timeline_scroll.bind("<B1-Motion>", self._drag_canvas_timeline)
        self.timeline_scroll.bind("<ButtonRelease-1>", self._end_canvas_timeline_drag)

        canvas_frame = tk.Frame(self.root, bg="#2b2b2b", padx=10, pady=10)
        canvas_frame.pack(expand=True, fill=tk.BOTH)
        self.canvas = tk.Canvas(canvas_frame, bg="#1a1a1a", cursor="crosshair", highlightthickness=0)
        self.canvas.pack(expand=True, fill=tk.BOTH)

    # ---------- PLAY/PAUSE ----------
    def toggle_play(self):
        self.is_playing = not self.is_playing
        if self.is_playing:
            self.active_frame_idx = 0
            self.playback_start_time = time.time()
            self.play_audio_for_animation()
            self.run_playback()
        else:
            if self.playback_job:
                self.root.after_cancel(self.playback_job)
                self.playback_job = None
            self.stop_playback_audio()
        self._update_play_button()

    def _update_play_button(self):
        if self.is_playing:
            img = self.load_icon("pause.png", base_size=(28, 28))
            if img:
                self.play_button.config(image=img)
                self.play_button.image = img
            else:
                self.play_button.config(text="⏸")
        else:
            img = self.load_icon("play.png", base_size=(28, 28))
            if img:
                self.play_button.config(image=img)
                self.play_button.image = img
            else:
                self.play_button.config(text="▶")

    # ---------- TIMELINE UI ----------
    def on_brush_select(self, event):
        selected = self.brush_var.get()
        if selected in self.brushes:
            self.current_brush_name = selected
            self.current_brush = self.brushes[selected]

    def _start_canvas_timeline_drag(self, event):
        canvas = self.timeline_scroll
        x = event.x_root - canvas.winfo_rootx()
        canvas.scan_mark(x, 0)
        self._canvas_timeline_drag = True
        return "break"

    def _drag_canvas_timeline(self, event):
        if not getattr(self, "_canvas_timeline_drag", False):
            return "break"
        canvas = self.timeline_scroll
        x = event.x_root - canvas.winfo_rootx()
        canvas.scan_dragto(x, 0, gain=1)
        self._scroll_position = canvas.xview()[0]
        self.update_visible_timeline_frames()
        return "break"

    def _end_canvas_timeline_drag(self, event):
        self._canvas_timeline_drag = False
        return "break"

    def refresh_timeline_ui(self):
        if hasattr(self, 'timeline_scroll') and self.timeline_scroll.winfo_exists():
            try: self._scroll_position = self.timeline_scroll.xview()[0]
            except: pass
        for w in self.timeline_inner.winfo_children():
            w.destroy()
        self.timeline_frame_widgets = []
        frame_width = 70
        padding = 6
        total_width = len(self.frames) * (frame_width + padding) + 20
        self.timeline_inner.config(width=total_width, height=70)
        self.timeline_scroll.itemconfigure(self.timeline_window, width=total_width, height=70)
        self.timeline_scroll.configure(scrollregion=(0, 0, total_width, 70))
        self._create_all_frame_cards()
        self.update_visible_timeline_frames()
        if hasattr(self, '_scroll_position') and not getattr(self, '_canvas_timeline_drag', False):
            self.root.after(10, lambda: self.timeline_scroll.xview_moveto(self._scroll_position))

    def _create_all_frame_cards(self):
        self.frame_cards = []
        self.frame_labels = []
        for idx, frame in enumerate(self.frames):
            is_active = (idx == self.active_frame_idx)
            bg = "#007acc" if is_active else "#333"
            card = tk.Frame(self.timeline_inner, bg=bg, padx=2, pady=2, relief=tk.RAISED, bd=1)
            card.idx = idx
            card.is_active = is_active
            label = tk.Label(card, text=f"F{idx+1}", bg=bg, fg="white", width=6, height=3, font=("Arial", 9, "bold"))
            label.pack()
            for widget in (card, label):
                widget.bind("<ButtonPress-1>", lambda e, c=card: self._start_frame_drag(e, c))
                widget.bind("<B1-Motion>", lambda e, c=card: self._drag_frame(e, c))
                widget.bind("<ButtonRelease-1>", lambda e, c=card: self._end_frame_drag(e, c))
            self.frame_cards.append(card)
            self.frame_labels.append(label)

    def _start_frame_drag(self, event, card):
        canvas = self.timeline_scroll
        x = event.x_root - canvas.winfo_rootx()
        self._frame_drag = {"card": card, "start_x": event.x_root, "dragging": False}
        canvas.scan_mark(x, 0)

    def _drag_frame(self, event, card):
        drag = getattr(self, "_frame_drag", None)
        if not drag or drag["card"] is not card:
            return "break"
        if not drag["dragging"] and abs(event.x_root - drag["start_x"]) >= 5:
            drag["dragging"] = True
        if drag["dragging"]:
            canvas = self.timeline_scroll
            x = event.x_root - canvas.winfo_rootx()
            canvas.scan_dragto(x, 0, gain=1)
            self._scroll_position = canvas.xview()[0]
            self.update_visible_timeline_frames()
        return "break"

    def _end_frame_drag(self, event, card):
        drag = getattr(self, "_frame_drag", None)
        if not drag or drag["card"] is not card:
            return "break"
        try:
            if not drag["dragging"]:
                self.select_frame(card.idx)
        finally:
            self._frame_drag = None
        return "break"

    def update_visible_timeline_frames(self):
        if not hasattr(self, 'frame_cards'):
            return
        canvas = self.timeline_scroll
        canvas_width = canvas.winfo_width()
        if canvas_width <= 0: return
        x1 = canvas.canvasx(0)
        x2 = canvas.canvasx(canvas_width)
        margin = 100
        x1 -= margin
        x2 += margin
        for idx, card in enumerate(self.frame_cards):
            x_pos = idx * 76 + 5
            if x1 <= x_pos <= x2:
                if not card.winfo_ismapped():
                    card.place(x=x_pos, y=2)
            else:
                if card.winfo_ismapped():
                    card.place_forget()
        for idx, card in enumerate(self.frame_cards):
            is_active = (idx == self.active_frame_idx)
            bg = "#007acc" if is_active else "#333"
            card.config(bg=bg)
            if idx < len(self.frame_labels):
                self.frame_labels[idx].config(bg=bg)

    # ---------- COLOR WHEEL ----------
    def draw_color_wheel(self):
        cx, cy = self.wheel_size // 2, self.wheel_size // 2
        r = (self.wheel_size // 2) - 10
        for deg in range(360):
            hue = deg / 360.0
            r_val, g_val, b_val = [int(c * 255) for c in colorsys.hsv_to_rgb(hue, 1.0, 1.0)]
            hex_color = f"#{r_val:02x}{g_val:02x}{b_val:02x}"
            self.wheel_canvas.create_arc(cx - r, cy - r, cx + r, cy + r,
                                         start=deg, extent=1.8, fill=hex_color, outline=hex_color)
        self.wheel_canvas.create_oval(cx - r, cy - r, cx + r, cy + r, outline="white", width=1)
        tri_y = cy + r + 2
        self.wheel_canvas.create_polygon(cx - 10, tri_y, cx + 10, tri_y, cx, tri_y + 10, fill="white", outline="gray")

    def on_wheel_click(self, event):
        cx, cy = self.wheel_size // 2, self.wheel_size // 2
        r = (self.wheel_size // 2) - 10
        dx = event.x - cx
        dy = event.y - cy
        dist = math.hypot(dx, dy)
        if dist <= r:
            angle = math.atan2(-dy, dx)
            deg = math.degrees(angle) % 360
            hue = deg / 360.0
            sat = min(1.0, dist / r)
            r_val, g_val, b_val = [int(c * 255) for c in colorsys.hsv_to_rgb(hue, sat, 1.0)]
            hex_color = f"#{r_val:02x}{g_val:02x}{b_val:02x}"
            self.set_active_color(hex_color)

    def on_wheel_double_click(self, event):
        color = colorchooser.askcolor(title="Choose Color", color=self.current_color)
        if color and color[1]:
            self.set_active_color(color[1])

    def set_active_color(self, hex_color):
        self.current_color = hex_color
        self.color_preview.config(bg=hex_color)
        if self.text_control_window and self.text_control_window.winfo_exists():
            try: self.color_preview_btn.config(bg=self.current_color)
            except: pass

    def save_current_color(self):
        self.swatch_colors[self.save_index] = self.current_color
        self.swatch_buttons[self.save_index].config(bg=self.current_color)
        self.save_index = (self.save_index + 1) % 9

    def select_swatch_color(self, idx):
        self.set_active_color(self.swatch_colors[idx])

    # ---------- LAYERS ----------
    def refresh_layers_ui(self):
        for w in self.layers_container.winfo_children():
            w.destroy()
        active_frame = self.frames[self.active_frame_idx]
        for layer in active_frame.layers:
            is_selected = (layer.id == self.active_layer_id)
            row_bg = "#555" if is_selected else "#444"
            layer_row = tk.Frame(self.layers_container, bg=row_bg, pady=3, padx=3,
                                 highlightbackground="#007acc" if is_selected else row_bg,
                                 highlightthickness=1)
            layer_row.pack(fill=tk.X, pady=2)
            lock_file = "locked.png" if layer.locked else "unlocked.png"
            smile_file = "smileyopen.png" if layer.visible else "smileyclosed.png"
            lock_img = self.load_icon(lock_file, base_size=(18, 18))
            smile_img = self.load_icon(smile_file, base_size=(18, 18))
            if smile_img:
                vis_btn = tk.Button(layer_row, image=smile_img, bg=row_bg, bd=0, relief=tk.FLAT,
                                    command=lambda lid=layer.id: self.toggle_layer_visibility(lid))
            else:
                vis_btn = tk.Button(layer_row, text="V" if layer.visible else "H", bg=row_bg, fg="white", bd=0,
                                    command=lambda lid=layer.id: self.toggle_layer_visibility(lid))
            vis_btn.pack(side=tk.RIGHT, padx=2)
            if lock_img:
                lock_btn = tk.Button(layer_row, image=lock_img, bg=row_bg, bd=0, relief=tk.FLAT,
                                     command=lambda lid=layer.id: self.toggle_layer_lock(lid))
            else:
                lock_btn = tk.Button(layer_row, text="L" if layer.locked else "U", bg=row_bg, fg="white", bd=0,
                                     command=lambda lid=layer.id: self.toggle_layer_lock(lid))
            lock_btn.pack(side=tk.RIGHT, padx=2)
            lbl = tk.Label(layer_row, text=layer.name, bg=row_bg, fg="white",
                           font=("Arial", 10, "bold" if is_selected else "normal"), anchor="w")
            lbl.pack(side=tk.LEFT, padx=5, expand=True, fill=tk.X)
            layer_row.bind("<Button-1>", lambda e, lid=layer.id: self.select_layer(lid))
            lbl.bind("<Button-1>", lambda e, lid=layer.id: self.select_layer(lid))

    def add_layer(self):
        new_id = self.next_layer_id
        self.next_layer_id += 1
        name = f"Layer {new_id}"
        for frame in self.frames:
            frame.layers.insert(0, Layer(new_id, name, self.canvas_width, self.canvas_height))
        self.active_layer_id = new_id
        self.refresh_layers_ui()
        self.render_canvas()

    def delete_active_layer(self):
        active_frame = self.frames[self.active_frame_idx]
        if len(active_frame.layers) <= 1:
            self.show_alert("Cannot Delete", "You must keep at least one layer!")
            return
        for frame in self.frames:
            frame.layers = [l for l in frame.layers if l.id != self.active_layer_id]
        self.active_layer_id = self.frames[self.active_frame_idx].layers[0].id
        self.refresh_layers_ui()
        self.render_canvas()

    def select_layer(self, layer_id):
        self.active_layer_id = layer_id
        self.refresh_layers_ui()

    def toggle_layer_visibility(self, layer_id):
        active_frame = self.frames[self.active_frame_idx]
        layer = active_frame.get_layer(layer_id)
        if layer:
            layer.visible = not layer.visible
            self.refresh_layers_ui()
            self.render_canvas()

    def toggle_layer_lock(self, layer_id):
        active_frame = self.frames[self.active_frame_idx]
        layer = active_frame.get_layer(layer_id)
        if layer:
            layer.locked = not layer.locked
            self.refresh_layers_ui()

    def select_frame(self, frame_idx):
        if 0 <= frame_idx < len(self.frames):
            self.active_frame_idx = frame_idx
            self.update_visible_timeline_frames()
            self.refresh_layers_ui()
            self.render_canvas()

    def add_frame(self):
        self.save_undo_state()
        new_frame_id = len(self.frames) + 1
        new_layers = [Layer(l.id, l.name, self.canvas_width, self.canvas_height)
                      for l in self.frames[0].layers]
        new_frame = Frame(new_frame_id, new_layers)
        self.frames.insert(self.active_frame_idx + 1, new_frame)
        self.active_frame_idx += 1
        self.refresh_timeline_ui()
        self.render_canvas()

    def duplicate_frame(self):
        self.save_undo_state()
        curr_frame = self.frames[self.active_frame_idx]
        dup_frame = Frame(len(self.frames) + 1, curr_frame.layers)
        self.frames.insert(self.active_frame_idx + 1, dup_frame)
        self.active_frame_idx += 1
        self.refresh_timeline_ui()
        self.render_canvas()

    def delete_frame(self):
        if len(self.frames) <= 1:
            self.show_alert("Cannot Delete", "You must keep at least one frame!")
            return
        self.save_undo_state()
        self.frames.pop(self.active_frame_idx)
        self.active_frame_idx = max(0, self.active_frame_idx - 1)
        self.refresh_timeline_ui()
        self.render_canvas()

    def toggle_onion_skin(self):
        self.onion_skin = not self.onion_skin
        self.onion_btn.config(text="Onion Skin: ON" if self.onion_skin else "Onion Skin: OFF",
                              bg="#007acc" if self.onion_skin else "#555")
        self.render_canvas()

    def run_playback(self):
        if not self.is_playing:
            return
        self.active_frame_idx = (self.active_frame_idx + 1) % len(self.frames)
        self.update_visible_timeline_frames()
        self.refresh_layers_ui()
        self.render_canvas()
        interval = max(10, int(1000 / self.fps))
        self.playback_job = self.root.after(interval, self.run_playback)

    def first_frame(self):
        self.select_frame(0)
    def last_frame(self):
        self.select_frame(len(self.frames) - 1)

    def render_canvas(self):
        composite = Image.new("RGBA", (self.canvas_width, self.canvas_height), (255, 255, 255, 255))
        if self.onion_skin and self.active_frame_idx > 0 and not self.is_playing:
            prev_frame = self.frames[self.active_frame_idx - 1]
            prev_comp = Image.new("RGBA", (self.canvas_width, self.canvas_height), (0, 0, 0, 0))
            for layer in reversed(prev_frame.layers):
                if layer.visible:
                    prev_comp.alpha_composite(layer.image)
            r, g, b, a = prev_comp.split()
            a = a.point(lambda p: int(p * 0.35))
            prev_ghost = Image.merge("RGBA", (r, g, b, a))
            composite.alpha_composite(prev_ghost)
        active_frame = self.frames[self.active_frame_idx]
        for layer in reversed(active_frame.layers):
            if layer.visible:
                composite.alpha_composite(layer.image)
        scaled_w = int(self.canvas_width * self.zoom_level)
        scaled_h = int(self.canvas_height * self.zoom_level)
        if self.zoom_level != 1.0:
            resample_mode = NEAREST_NEIGHBOR if self.brush_mode == "pixel" else BILINEAR
            displayed_img = composite.resize((scaled_w, scaled_h), resample_mode)
        else:
            displayed_img = composite
        self.tk_canvas_img = ImageTk.PhotoImage(displayed_img)
        self.canvas.delete("all")
        cw = self.canvas.winfo_width() or 800
        ch = self.canvas.winfo_height() or 600
        center_x = (cw / 2) + self.pan_offset_x
        center_y = (ch / 2) + self.pan_offset_y
        self.canvas.create_image(center_x, center_y, image=self.tk_canvas_img, anchor=tk.CENTER)
        self.img_top_left_x = center_x - (scaled_w / 2)
        self.img_top_left_y = center_y - (scaled_h / 2)

    def screen_to_canvas_coords(self, sx, sy):
        cx = int((sx - self.img_top_left_x) / self.zoom_level)
        cy = int((sy - self.img_top_left_y) / self.zoom_level)
        return cx, cy

    def on_size_change(self, val):
        self.brush_size = int(val)
        self.size_label.config(text=f"{self.brush_size}pt")

    def select_tool(self, tool_id):
        if tool_id == "undo":
            self.undo()
            return
        elif tool_id == "redo":
            self.redo()
            return
        if self.text_mode and tool_id != "text":
            self.cancel_text()
        if tool_id not in ["marquee", "selection"]:
            self.clear_selection()
        self.current_tool = tool_id
        if tool_id == "text":
            self.text_mode = True
            self.text_string = ""
            self.text_position = (self.canvas_width // 2, self.canvas_height // 2)
            self.show_alert("Text Tool", "Click to place text.")
            return
        for t_id, btn in self.tool_buttons.items():
            btn.config(bg="#555555" if t_id == tool_id else "#2a2a2a")

    def reset_view(self):
        self.zoom_level = 1.0
        self.pan_offset_x = 0
        self.pan_offset_y = 0
        self.render_canvas()

    def save_undo_state(self):
        curr_frame = self.frames[self.active_frame_idx]
        layer = curr_frame.get_layer(self.active_layer_id)
        if layer:
            self.undo_stack.append((self.active_frame_idx, self.active_layer_id, layer.image.copy()))
            if len(self.undo_stack) > 30:
                self.undo_stack.pop(0)
            self.redo_stack.clear()

    def undo(self):
        if not self.undo_stack:
            return
        f_idx, l_id, img_copy = self.undo_stack.pop()
        curr_layer = self.frames[f_idx].get_layer(l_id)
        if curr_layer:
            self.redo_stack.append((f_idx, l_id, curr_layer.image.copy()))
            curr_layer.image = img_copy
            self.render_canvas()

    def redo(self):
        if not self.redo_stack:
            return
        f_idx, l_id, img_copy = self.redo_stack.pop()
        curr_layer = self.frames[f_idx].get_layer(l_id)
        if curr_layer:
            self.undo_stack.append((f_idx, l_id, curr_layer.image.copy()))
            curr_layer.image = img_copy
            self.render_canvas()

    def clear_active_layer(self):
        self.save_undo_state()
        layer = self.frames[self.active_frame_idx].get_layer(self.active_layer_id)
        if layer:
            layer.image = Image.new("RGBA", (self.canvas_width, self.canvas_height), (0, 0, 0, 0))
            self.render_canvas()

    def bind_canvas_events(self):
        self.canvas.bind("<ButtonPress-1>", self.on_draw_start)
        self.canvas.bind("<B1-Motion>", self.on_draw_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_draw_stop)
        self.canvas.bind("<ButtonPress-2>", self.on_pan_start)
        self.canvas.bind("<B2-Motion>", self.on_pan_motion)
        self.canvas.bind("<ButtonPress-3>", self.on_pan_start)
        self.canvas.bind("<B3-Motion>", self.on_pan_motion)
        self.canvas.bind("<ButtonRelease-3>", self.on_canvas_right_click)

    def on_canvas_right_click(self, event):
        if self.text_mode and self.text_string:
            self.text_scale_mode = not self.text_scale_mode
            self.render_text_preview()

    def get_active_layer_object(self):
        active_frame = self.frames[self.active_frame_idx]
        layer = active_frame.get_layer(self.active_layer_id)
        if layer and layer.visible and not layer.locked:
            return layer
        return None

    def hex_to_rgba(self, hex_color, alpha=255):
        hex_color = hex_color.lstrip('#')
        return tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4)) + (alpha,)

    def pick_color(self, cx, cy):
        active_frame = self.frames[self.active_frame_idx]
        composite = Image.new("RGBA", (self.canvas_width, self.canvas_height), (255, 255, 255, 255))
        for layer in reversed(active_frame.layers):
            if layer.visible:
                composite.alpha_composite(layer.image)
        if 0 <= cx < self.canvas_width and 0 <= cy < self.canvas_height:
            r, g, b, a = composite.getpixel((cx, cy))
            self.set_active_color(f"#{r:02x}{g:02x}{b:02x}")

    def on_pan_start(self, event):
        self.start_pan_x = event.x - self.pan_offset_x
        self.start_pan_y = event.y - self.pan_offset_y
    def on_pan_motion(self, event):
        self.pan_offset_x = event.x - self.start_pan_x
        self.pan_offset_y = event.y - self.start_pan_y
        self.render_canvas()

    def import_mp4(self):
        if not self.check_ffmpeg_installed():
            return
        path = filedialog.askopenfilename(filetypes=[("Video Files", "*.mp4 *.avi *.mov *.mkv")])
        if not path:
            return
        with tempfile.TemporaryDirectory() as temp_dir:
            out_pattern = os.path.join(temp_dir, "frame_%05d.png")
            cmd = ["ffmpeg", "-y", "-i", path, out_pattern]
            subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            frame_files = sorted([os.path.join(temp_dir, f) for f in os.listdir(temp_dir) if f.endswith(".png")])
            if not frame_files:
                return
            imported_frames = []
            for idx, fpath in enumerate(frame_files):
                img = Image.open(fpath).convert("RGBA").resize((self.canvas_width, self.canvas_height), BILINEAR)
                layers = [Layer(1, "Layer 1", self.canvas_width, self.canvas_height)]
                layers[0].image = img
                imported_frames.append(Frame(idx + 1, layers))
            self.frames = imported_frames
            self.refresh_timeline_ui()
            self.render_canvas()

    def export_gif(self):
        path = filedialog.asksaveasfilename(defaultextension=".gif")
        if not path:
            return
        rendered_frames = []
        for frame in self.frames:
            comp = Image.new("RGBA", (self.canvas_width, self.canvas_height), (255, 255, 255, 255))
            for layer in reversed(frame.layers):
                if layer.visible:
                    comp.alpha_composite(layer.image)
            rendered_frames.append(comp.convert("RGB"))
        rendered_frames[0].save(path, save_all=True, append_images=rendered_frames[1:], duration=int(1000/self.fps), loop=0)

    def export_png_sequence(self):
        folder = filedialog.askdirectory()
        if not folder:
            return
        for idx, frame in enumerate(self.frames):
            comp = Image.new("RGBA", (self.canvas_width, self.canvas_height), (0, 0, 0, 0))
            for layer in reversed(frame.layers):
                if layer.visible:
                    comp.alpha_composite(layer.image)
            comp.save(os.path.join(folder, f"frame_{idx+1:04d}.png"), "PNG")

    def save_project(self):
        path = filedialog.asksaveasfilename(defaultextension=".anim")
        if not path:
            return
        try:
            project_data = {
                "canvas_width": self.canvas_width,
                "canvas_height": self.canvas_height,
                "fps": self.fps,
                "next_layer_id": self.next_layer_id,
                "active_layer_id": self.active_layer_id,
                "active_frame_idx": self.active_frame_idx,
                "audio_clips": self.audio_clips,
                "frames": []
            }
            for frame in self.frames:
                frame_data = {"id": frame.id, "layers": []}
                for layer in frame.layers:
                    buf = io.BytesIO()
                    layer.image.save(buf, format="PNG")
                    frame_data["layers"].append({
                        "id": layer.id,
                        "name": layer.name,
                        "visible": layer.visible,
                        "locked": layer.locked,
                        "image_bytes": buf.getvalue()
                    })
                project_data["frames"].append(frame_data)
            with open(path, "wb") as f:
                pickle.dump(project_data, f)
        except Exception as e:
            self.show_error_dialog(str(e))

    def load_project(self):
        path = filedialog.askopenfilename(filetypes=[("Freenimate Project", "*.anim")])
        if not path:
            return
        try:
            with open(path, "rb") as f:
                project_data = pickle.load(f)
            self.canvas_width = project_data["canvas_width"]
            self.canvas_height = project_data["canvas_height"]
            self.fps = project_data["fps"]
            loaded_frames = []
            for frame_data in project_data["frames"]:
                base_layers = []
                for layer_data in frame_data["layers"]:
                    layer = Layer(layer_data["id"], layer_data["name"], self.canvas_width, self.canvas_height)
                    layer.image = Image.open(io.BytesIO(layer_data["image_bytes"])).convert("RGBA")
                    layer.visible = layer_data["visible"]
                    layer.locked = layer_data["locked"]
                    base_layers.append(layer)
                loaded_frames.append(Frame(frame_data["id"], base_layers))
            self.frames = loaded_frames
            self.audio_clips = project_data.get("audio_clips", [])
            self.refresh_timeline_ui()
            self.render_canvas()
        except Exception as e:
            self.show_error_dialog(str(e))

    def show_traceback_error(self, error_text=None):
        if error_text is None:
            error_text = traceback.format_exc()
        if len(error_text) > 500:
            error_text = error_text[:500] + "\n... (truncated)"
        self.show_error_dialog(f"An error occurred:\n\n{error_text}")

if __name__ == "__main__":
    root = tk.Tk()
    app = FreenimateApp(root)
    root.mainloop()