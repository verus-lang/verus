#!/usr/bin/env python

import argparse
import json
import glob
from matplotlib import pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages
import numpy as np
import os

def plot_survival_curve(times, name, total_solved, errors):
    # Calculate survival curve
    perf = np.array(np.sort(times))
    cdf = np.cumsum(perf)
    plt.plot(cdf, np.arange(0, len(cdf)), label=name, linestyle="solid", color="black")
    plt.title(f"{name} - Solved {total_solved}, with {errors} errors")
    plt.ylim(0)
    plt.xlim(0.1)
    plt.xscale("log")
    plt.xlabel("Time Log Scale (ms)")
    plt.ylabel("Instances Soveld")
    plt.grid()
    os.makedirs("fig/survival", exist_ok=True)
    plt.savefig(f"fig/survival/{name}.pdf")
    plt.close()

class FunctionSmtTime:
    def __init__(self, json):
        self.name = json["function"]
        self.time_ms = json["time"]
        if "success" in json:
            self.success = json["success"]
        else:
            print(f"Failed to find a success entry in {json}")
            self.success = False

    def __str__(self):
        return f'{self.name} <{self.time_ms}>'

class Project:
    def __init__(self, json):
        self.name = json["runner"]["run_configuration"]["name"]
        self.refspec = json["runner"]["run_configuration"]["refspec"]
        self.times_ms = json["times-ms"]
        if "verified" in json["verification-results"]:
            self.total_solved = json["verification-results"]["verified"]
        else:
            self.total_solved = 0
        if "errors" in json["verification-results"]:
            self.errors = json["verification-results"]["errors"]
        else:
            self.errors = 0
        self.run_label = json["runner"]["label"]
        self.date = json["runner"]["date"] if "date" in json["runner"] else json["runner"]["data"]

        # Collect SMT times
        self.fn_smt_times = []
        if "smt" in self.times_ms:
            for item in self.times_ms["smt"]["smt-run-module-times"]:
                for function in item["function-breakdown"]:
                    self.fn_smt_times.append(FunctionSmtTime(function))

        print(f"Total errors: {self.errors}; counted errors: {len([f for f in self.fn_smt_times if not f.success])}")

    def __str__(self):
        return f'{self.name} <{self.refspec}>'

    def get_smt_times(self):
        return [f.time_ms for f in self.fn_smt_times if f.success]

    def plot_survival_curve(self):
        plot_survival_curve(self.get_smt_times(), self.name, self.total_solved, self.errors)


def read_json_files_into_projects(directory):
    projects = []
    for filename in glob.glob(f'{directory}/*.json'):
        with open(filename, 'r') as file:
            projects.append(Project(json.load(file)))
    return projects

class Run:
    def __init__(self, directory):
        self.directory = directory
        self.projects = read_json_files_into_projects(directory)
        self.label = self.projects[0].run_label
        self.date = self.projects[0].date

        self.total_solved = sum([project.total_solved for project in self.projects])
        self.errors = sum([project.errors for project in self.projects])

    def get_smt_times(self):
        return [f.time_ms for project in self.projects for f in project.fn_smt_times if f.success]

    def __str__(self):
        return f'{self.project} <{self.time_ms}>'

    def get_project_names(self):
        return [project.name for project in self.projects]
    
    def get_project(self, name):
        for project in self.projects:
            if project.name == name:
                return project
        return None

    def plot_survival_curve(self):
        plot_survival_curve(self.get_smt_times(), f'{self.label} ({self.date})', self.total_solved, self.errors)

    def plot_survival_curves(self):
        self.plot_survival_curve()
        for project in self.projects:
            project.plot_survival_curve()

def plot_runs_overall(pdf, name, runs):
    plt.figure()
    for run in runs:
        # Calculate survival curve
        times = run.get_smt_times()
        perf = np.array(np.sort(times))
        cdf = np.cumsum(perf)
        label = f"{run.label} ({run.total_solved} verified; {run.errors} errors)"
        plt.plot(cdf, np.arange(0, len(cdf)), label=label, linestyle="solid")
    plt.legend()
    plt.ylim(0)
    plt.xlim(0.1)
    plt.title(name)
    plt.xscale("log")
    plt.xlabel("Time Log Scale (ms)")
    plt.ylabel("Functions Verified")
    plt.grid()
    pdf.savefig()

def plot_runs_per_project(pdf, runs):
    for project_name in sorted(runs[0].get_project_names()):
        plt.figure()
        for run in runs:
            # Calculate survival curve
            project = run.get_project(project_name)
            times = project.get_smt_times()
            perf = np.array(np.sort(times))
            cdf = np.cumsum(perf)
            label = f"{run.label} ({project.total_solved} verified; {project.errors} errors)"
            plt.plot(cdf, np.arange(0, len(cdf)), label=label, linestyle="solid")
        plt.legend()
        plt.ylim(0)
        plt.xlim(0.1)
        plt.title(project_name)
        plt.xscale("log")
        plt.xlabel("Time Log Scale (ms)")
        plt.ylabel("Functions Verified")
        plt.grid()
        pdf.savefig()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('dirs', nargs='+', help='One or more directories of results to analyze')
    args = parser.parse_args()

    runs = [Run(d) for d in args.dirs]
    os.makedirs("fig/survival", exist_ok=True)
    with PdfPages('fig/survival/results.pdf') as pdf:
        plot_runs_overall(pdf, "all projects", runs)
        plot_runs_per_project(pdf, runs)

if __name__ == '__main__':
    main()
