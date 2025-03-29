import tkinter as tk
from tkinter import ttk, Frame, Button, Label, Canvas, Scrollbar, Checkbutton, IntVar, StringVar, filedialog
import colorsys
import math
import time
import uuid
import os
import networkx as nx
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from collections import defaultdict, Counter
import threading

# Global variables
proof_trace = {
    'nodes': [],              # List of node IDs
    'edges': [],              # List of (parent, child) tuples
    'node_attributes': {},    # Dict mapping node ID to attributes
    'call_count': 0,          # Total number of function calls
    'hit_count': 0,           # Number of times a cached result was used
    'success_count': 0,       # Number of successful proof attempts
    'failure_count': 0        # Number of failed proof attempts
}

# Node counter for generating unique IDs
node_counter = 0

def initialize_trace():
    """Initialize the proof trace data structure"""
    global proof_trace, node_counter
    proof_trace = {
        'nodes': [],
        'edges': [],
        'node_attributes': {},
        'call_count': 0,
        'hit_count': 0,
        'success_count': 0,
        'failure_count': 0
    }
    node_counter = 0

def track_proof_step(goal, rule, result, depth, parent_id=None):
    """Track a step in the proof search for visualization"""
    global proof_trace, node_counter
    
    # Generate a unique node ID
    node_id = node_counter
    node_counter += 1
    
    # Store the node
    proof_trace['nodes'].append(node_id)
    proof_trace['node_attributes'][node_id] = {
        'goal': goal,
        'rule': rule,
        'result': result,
        'depth': depth,
        'id': node_id
    }
    
    # Add edge to parent if it exists
    if parent_id is not None:
        proof_trace['edges'].append((parent_id, node_id))
    
    # Update statistics
    proof_trace['call_count'] += 1
    
    # Return the node ID for use in recursive calls
    return node_id

def update_node_result(node_id, result):
    """Update a node's result after processing"""
    if node_id in proof_trace['node_attributes']:
        proof_trace['node_attributes'][node_id]['result'] = result
        
        # Update statistics
        if result:
            proof_trace['success_count'] += 1
        else:
            proof_trace['failure_count'] += 1

def print_statistics():
    """Print statistics about the proof search"""
    print("\n--- Proof Search Statistics ---")
    print(f"Total function calls: {proof_trace['call_count']}")
    print(f"Successful calls: {proof_trace['success_count']}")
    print(f"Failed calls: {proof_trace['failure_count']}")
    if proof_trace['call_count'] > 0:
        hit_rate = (proof_trace['hit_count'] / proof_trace['call_count']) * 100
        print(f"Cache hit rate: {hit_rate:.2f}%")
    print("-----------------------------")

def visualize_proof_search(save_path=None, animate=False):
    """Generate a visualization of the proof search using NetworkX and matplotlib"""
    # Create a directed graph
    G = nx.DiGraph()
    
    # Add nodes to the graph
    for node_id in proof_trace['nodes']:
        attrs = proof_trace['node_attributes'][node_id]
        G.add_node(node_id, **attrs)
    
    # Add edges to the graph
    for parent, child in proof_trace['edges']:
        G.add_edge(parent, child)
    
    # Create node color map
    node_colors = []
    for node in G.nodes():
        if G.nodes[node]['result'] is True:
            node_colors.append('green')
        elif G.nodes[node]['result'] is False:
            node_colors.append('red')
        else:
            node_colors.append('gray')
    
    # Create the figure
    plt.figure(figsize=(12, 10))
    
    # Use spring layout since graphviz might not be available
    pos = nx.spring_layout(G, k=0.5, iterations=100)
    
    # Draw the graph
    nx.draw(G, pos, with_labels=True, node_color=node_colors, 
            node_size=300, alpha=0.8, arrows=True,
            labels={n: G.nodes[n]['rule'] for n in G.nodes()})
    
    # Add a title
    plt.title("Proof Search Visualization")
    
    # Save the visualization if requested
    if save_path:
        plt.savefig(save_path)
    
    # Show the visualization
    plt.show()
    
    # Create an animation if requested
    if animate:
        create_animated_visualization(G, pos, save_path)

def create_animated_visualization(G, pos, save_path=None):
    """Create a step-by-step animation of the proof search"""
    fig, ax = plt.subplots(figsize=(12, 10))
    
    # Sort nodes by their creation order
    sorted_nodes = sorted(G.nodes(), key=lambda n: n)
    sorted_edges = []
    
    # Collect edges in order
    for node in sorted_nodes:
        for _, child in G.out_edges(node):
            sorted_edges.append((node, child))
    
    def update(num):
        ax.clear()
        
        # Determine which nodes and edges to show in this frame
        current_nodes = sorted_nodes[:num+1]
        current_edges = [(u, v) for u, v in sorted_edges if u in current_nodes and v in current_nodes]
        
        # Create subgraph for current frame
        sub_G = G.subgraph(current_nodes)
        
        # Create color map for nodes
        node_colors = []
        for node in sub_G.nodes():
            if G.nodes[node]['result'] is True:
                node_colors.append('green')
            elif G.nodes[node]['result'] is False:
                node_colors.append('red')
            else:
                node_colors.append('gray')
        
        # Draw the graph
        nx.draw(sub_G, pos, with_labels=True, node_color=node_colors, 
                node_size=300, alpha=0.8, arrows=True,
                labels={n: G.nodes[n]['rule'] for n in sub_G.nodes()},
                ax=ax)
        
        ax.set_title(f"Proof Search Step {num+1}/{len(sorted_nodes)}")
    
    # Create the animation
    ani = animation.FuncAnimation(fig, update, frames=len(sorted_nodes), interval=200, repeat=True)
    
    # Save the animation if requested
    if save_path:
        if not save_path.lower().endswith('.gif'):
            save_path = save_path.rsplit('.', 1)[0] + '.gif'
        ani.save(save_path, writer='pillow', fps=2)
    
    plt.show()

class VisualizerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Logic Bot Visualizer")
        self.root.geometry("1200x800")
        
        # Set dark theme
        self.dark_mode = IntVar(value=1)
        self.apply_theme()
        
        # Create frames
        self.create_frames()
        
        # Create controls
        self.create_controls()
        
        # Create network graph
        self.graph = nx.DiGraph()
        
        # Create visualization canvas
        self.create_visualization()
        
        # Animation variables
        self.animation_speed = 500  # milliseconds
        self.current_step = 0
        self.is_animating = False
        self.animation_thread = None
        
        # Keep track of cached results
        self.memoization_cache = {}
        
        # Update the statistics
        self.update_statistics()
    
    def apply_theme(self):
        # Apply dark or light theme based on self.dark_mode
        if self.dark_mode.get():
            # Dark theme
            bg_color = "#1e1e1e"
            fg_color = "#ffffff"
            accent_color = "#3a3a3a"
            highlight_color = "#007acc"
        else:
            # Light theme
            bg_color = "#f0f0f0"
            fg_color = "#000000"
            accent_color = "#d9d9d9"
            highlight_color = "#007acc"
        
        # Set theme variables
        self.root.configure(bg=bg_color)
        self.theme_colors = {
            "bg": bg_color,
            "fg": fg_color,
            "accent": accent_color,
            "highlight": highlight_color
        }
        
        # Apply theme to all existing widgets
        for widget in self.root.winfo_children():
            self.apply_theme_to_widget(widget)
    
    def apply_theme_to_widget(self, widget):
        # Apply theme to a single widget and its children
        widget_type = widget.winfo_class()
        
        if widget_type in ("TFrame", "Frame"):
            widget.configure(bg=self.theme_colors["bg"])
        elif widget_type in ("TButton", "Button"):
            widget.configure(bg=self.theme_colors["accent"], fg=self.theme_colors["fg"])
        elif widget_type in ("TLabel", "Label"):
            widget.configure(bg=self.theme_colors["bg"], fg=self.theme_colors["fg"])
        elif widget_type == "Canvas":
            widget.configure(bg=self.theme_colors["bg"], highlightbackground=self.theme_colors["accent"])
        
        # Recursively apply to children
        for child in widget.winfo_children():
            self.apply_theme_to_widget(child)
    
    def create_frames(self):
        # Main container frame
        self.main_frame = Frame(self.root, bg=self.theme_colors["bg"])
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Top frame for controls
        self.control_frame = Frame(self.main_frame, bg=self.theme_colors["bg"])
        self.control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Frame for statistics
        self.stats_frame = Frame(self.main_frame, bg=self.theme_colors["bg"])
        self.stats_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Bottom frame for visualization
        self.viz_frame = Frame(self.main_frame, bg=self.theme_colors["bg"])
        self.viz_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
    
    def create_controls(self):
        # Controls for visualization
        self.run_button = Button(self.control_frame, text="Run Example", bg=self.theme_colors["accent"], 
                                fg=self.theme_colors["fg"], command=self.run_example)
        self.run_button.pack(side=tk.LEFT, padx=5, pady=5)
        
        self.step_button = Button(self.control_frame, text="Step", bg=self.theme_colors["accent"], 
                                 fg=self.theme_colors["fg"], command=self.step_visualization)
        self.step_button.pack(side=tk.LEFT, padx=5, pady=5)
        
        self.play_button = Button(self.control_frame, text="Play", bg=self.theme_colors["accent"], 
                                 fg=self.theme_colors["fg"], command=self.toggle_animation)
        self.play_button.pack(side=tk.LEFT, padx=5, pady=5)
        
        self.reset_button = Button(self.control_frame, text="Reset", bg=self.theme_colors["accent"], 
                                  fg=self.theme_colors["fg"], command=self.reset_visualization)
        self.reset_button.pack(side=tk.LEFT, padx=5, pady=5)
        
        self.example_var = StringVar(value="Example 1")
        self.example_menu = ttk.Combobox(self.control_frame, textvariable=self.example_var, 
                                         values=["Example 1", "Example 2", "Example 3"])
        self.example_menu.pack(side=tk.LEFT, padx=5, pady=5)
        
        # Dark mode toggle
        self.dark_mode_check = Checkbutton(self.control_frame, text="Dark Mode", variable=self.dark_mode, 
                                          command=self.apply_theme, bg=self.theme_colors["bg"], fg=self.theme_colors["fg"])
        self.dark_mode_check.pack(side=tk.RIGHT, padx=5, pady=5)
        
        # Speed control
        self.speed_label = Label(self.control_frame, text="Speed:", bg=self.theme_colors["bg"], fg=self.theme_colors["fg"])
        self.speed_label.pack(side=tk.RIGHT, padx=5, pady=5)
        
        self.speed_scale = ttk.Scale(self.control_frame, from_=100, to=1000, value=500, 
                                    command=self.update_speed, orient=tk.HORIZONTAL, length=100)
        self.speed_scale.pack(side=tk.RIGHT, padx=5, pady=5)
        
        # Statistics labels
        self.stats_labels = {}
        stats = ["Calls", "Successful", "Failed", "Cache Hits", "Cache Rate"]
        
        for i, stat in enumerate(stats):
            label = Label(self.stats_frame, text=f"{stat}: 0", bg=self.theme_colors["bg"], fg=self.theme_colors["fg"])
            label.grid(row=0, column=i, padx=10, pady=5, sticky='w')
            self.stats_labels[stat.lower()] = label
    
    def create_visualization(self):
        # Create matplotlib figure for visualization
        self.figure = plt.Figure(figsize=(10, 8), dpi=100)
        self.ax = self.figure.add_subplot(111)
        
        # Create canvas
        self.canvas = FigureCanvasTkAgg(self.figure, self.viz_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Draw empty graph initially
        self.update_visualization()
    
    def update_speed(self, val):
        self.animation_speed = int(float(val))
    
    def update_statistics(self):
        # Update statistics labels
        self.stats_labels["calls"].config(text=f"Calls: {proof_trace['call_count']}")
        self.stats_labels["successful"].config(text=f"Successful: {proof_trace['success_count']}")
        self.stats_labels["failed"].config(text=f"Failed: {proof_trace['failure_count']}")
        self.stats_labels["cache hits"].config(text=f"Cache Hits: {proof_trace['hit_count']}")
        
        hit_rate = 0
        if proof_trace['call_count'] > 0:
            hit_rate = (proof_trace['hit_count'] / proof_trace['call_count']) * 100
        self.stats_labels["cache rate"].config(text=f"Cache Rate: {hit_rate:.2f}%")
    
    def run_example(self):
        # Reset current state
        initialize_trace()
        self.reset_visualization()
        
        # Get selected example
        example_num = int(self.example_var.get().split()[-1])
        
        # Examples matching those in logic_bot.py
        examples = [
            {
                "premises": ["p --> q", "p"],
                "conclusion": "q",
                "name": "Example 1: Modus Ponens"
            },
            {
                "premises": ["p --> q", "q --> r"],
                "conclusion": "p --> r",
                "name": "Example 2: Hypothetical Syllogism"
            },
            {
                "premises": ["!p & q", "r --> p", "!r --> s", "s --> t"],
                "conclusion": "t",
                "name": "Example 3: Complex Reasoning"
            }
        ]
        
        # Run the selected example
        from logic_bot import derive_proof, tokenize, parse
        
        example = examples[example_num - 1]
        
        # Use derive_proof with visualization enabled
        derive_proof(example["premises"], example["conclusion"], max_depth=10, visualize=True)
        
        # Update the graph and statistics
        self.build_graph_from_trace()
        self.update_statistics()
        self.current_step = 0
        self.update_visualization()
    
    def build_graph_from_trace(self):
        # Create a directed graph from the proof trace
        self.graph = nx.DiGraph()
        
        # Add nodes to the graph
        for node_id in proof_trace['nodes']:
            attrs = proof_trace['node_attributes'][node_id]
            self.graph.add_node(node_id, **attrs)
        
        # Add edges to the graph
        for parent, child in proof_trace['edges']:
            self.graph.add_edge(parent, child)
    
    def update_visualization(self):
        # Clear the previous visualization
        self.ax.clear()
        
        if not self.graph.nodes():
            # Draw empty graph if no nodes
            self.ax.text(0.5, 0.5, "No visualization data. Run an example first.", 
                         horizontalalignment='center', verticalalignment='center',
                         color=self.theme_colors["fg"])
            self.figure.set_facecolor(self.theme_colors["bg"])
            self.ax.set_facecolor(self.theme_colors["bg"])
            self.canvas.draw()
            return
        
        # Always use spring layout since graphviz might not be available
        pos = nx.spring_layout(self.graph, k=0.5, iterations=100)
        
        # Determine which nodes and edges to show in the current step
        if self.current_step == 0:
            current_nodes = []
            current_edges = []
        else:
            # Show nodes up to the current step
            sorted_nodes = sorted(self.graph.nodes())[:self.current_step]
            current_nodes = sorted_nodes
            current_edges = [(u, v) for u, v in self.graph.edges() if u in current_nodes and v in current_nodes]
        
        # Create subgraph for current step
        sub_graph = self.graph.subgraph(current_nodes)
        
        # Create color map for nodes
        node_colors = []
        for node in sub_graph.nodes():
            if self.graph.nodes[node]['result'] is True:
                node_colors.append('green')
            elif self.graph.nodes[node]['result'] is False:
                node_colors.append('red')
            else:
                node_colors.append('gray')
        
        # Set background color
        self.figure.set_facecolor(self.theme_colors["bg"])
        self.ax.set_facecolor(self.theme_colors["bg"])
        
        # Draw the graph
        nx.draw(sub_graph, pos, with_labels=True, node_color=node_colors, 
                node_size=300, alpha=0.8, arrows=True,
                labels={n: sub_graph.nodes[n]['rule'] for n in sub_graph.nodes()},
                edge_color=self.theme_colors["fg"],
                font_color=self.theme_colors["fg"],
                ax=self.ax)
        
        # Set title
        self.ax.set_title(f"Proof Search Visualization - Step {self.current_step}/{len(self.graph.nodes())}", 
                         color=self.theme_colors["fg"])
        
        # Redraw the canvas
        self.canvas.draw()
    
    def step_visualization(self):
        if self.graph.nodes():
            if self.current_step < len(self.graph.nodes()):
                self.current_step += 1
                self.update_visualization()
    
    def toggle_animation(self):
        if self.is_animating:
            # Stop animation
            self.is_animating = False
            self.play_button.config(text="Play")
            if self.animation_thread and self.animation_thread.is_alive():
                self.animation_thread.join()
        else:
            # Start animation
            self.is_animating = True
            self.play_button.config(text="Pause")
            self.animation_thread = threading.Thread(target=self.animate_visualization)
            self.animation_thread.daemon = True
            self.animation_thread.start()
    
    def animate_visualization(self):
        while self.is_animating and self.current_step < len(self.graph.nodes()):
            self.current_step += 1
            self.root.after(0, self.update_visualization)
            time.sleep(self.animation_speed / 1000.0)
        
        # Reset button when animation completes
        if self.current_step >= len(self.graph.nodes()):
            self.is_animating = False
            self.root.after(0, lambda: self.play_button.config(text="Play"))
    
    def reset_visualization(self):
        self.current_step = 0
        self.is_animating = False
        self.play_button.config(text="Play")
        self.update_visualization()

def launch_gui():
    """Launch the visualizer GUI"""
    root = tk.Tk()
    app = VisualizerGUI(root)
    root.mainloop()

# Allow importing without launching the GUI
if __name__ == "__main__":
    launch_gui()
